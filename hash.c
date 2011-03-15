#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include <pthread.h>

#define TRUE 1
#define FALSE 0

#define UNINITIALIZED (NULL)
typedef unsigned int hash_t;
typedef void* key_t;
typedef void* value_t;
typedef int boolean;

#define PTR_TO_UINT(p) ((unsigned)(uintptr_t)p)
#define UINT_TO_PTR(p) ((void*)(uintptr_t)p)

#define LOAD_FACTOR 0.75f

typedef struct _node node_t;

typedef node_t* mark_ptr_t;

struct _node {
	mark_ptr_t next;
	hash_t hash_code;
	key_t key;
	value_t value;
};

typedef struct {
	mark_ptr_t *table;
	unsigned count, size;
} conc_hashtable_t;

/*FIXME, make this use a table*/
static hash_t
reverse_value (hash_t k)
{
	int i;
	hash_t r = 0;
	for (i = 0; i < 32; ++i) {
		hash_t bit = (k & (1 << i)) >> i;
		r |= bit << (31 - i);
	}
	return r;
}

static inline hash_t
hash_key (key_t key)
{
	return (hash_t)((uintptr_t)(key) * 2654435761u);
}

static inline hash_t
hash_regular_key (hash_t k)
{
	return reverse_value (k | 0x80000000);
}

static inline hash_t
hash_dummy_key (hash_t k)
{
	return reverse_value (k & ~0x80000000);
}

#define atomic_fetch_and_inc(t) __sync_fetch_and_add (t, 1)
#define atomic_fetch_and_dec(t) __sync_fetch_and_sub (t, 1)
#define atomic_compare_and_swap(t,old,new) __sync_bool_compare_and_swap (t, old, new)

#define load_barrier __builtin_ia32_lfence
#define store_barrier __builtin_ia32_sfence
#define memory_barrier __builtin_ia32_mfence

#define atomic_load(p)  ({ load_barrier (), *(p); })
#define atomic_store(p, v) do { store_barrier (); *(p) = v; } while (0);

static inline mark_ptr_t
mk_node (node_t *n, uintptr_t bit)
{
	return  (mark_ptr_t)(((uintptr_t)n) | bit);
}

static inline node_t*
get_node (mark_ptr_t n)
{
	return  (node_t*)(((uintptr_t)n) & ~(uintptr_t)0x1);
}

static inline uintptr_t
get_bit (mark_ptr_t n)
{
	return  (uintptr_t)n & 0x1;
}

static void
delete_node (mark_ptr_t node)
{
	assert (get_bit (node) == 0);
//	free (get_node (node));
}

static mark_ptr_t
list_find (mark_ptr_t *head, key_t key, hash_t hash_code, mark_ptr_t **out_prev)
{
	mark_ptr_t cur, next, *prev;
try_again:
	prev = head;
	cur = atomic_load (prev);
	while (1) {
		if (cur == NULL)
			goto done;
		next = cur->next;
		hash_t cur_hash = cur->hash_code;
		key_t cur_key = cur->key;

		if (atomic_load (prev) != mk_node (get_node (cur), 0))
			goto try_again;

		if (!get_bit (next)) {
			if (cur_hash > hash_code || (cur_hash == hash_code && cur_key == key))
				goto done;

			prev = &get_node (cur)->next;
		} else {
			if (atomic_compare_and_swap (prev, mk_node (get_node (cur), 0), mk_node (get_node (next), 0)))
				delete_node (get_node (cur));
			else
				goto try_again;
		}
		cur = next;
	}
done:
	*out_prev = prev;
	return cur;
}

static mark_ptr_t
list_insert (mark_ptr_t *head, node_t *node)
{
	mark_ptr_t res, *prev;
	key_t key = node->key;
	hash_t hash_code = node->hash_code;

	while (1) {
		res = list_find (head, key, hash_code, &prev);
		if (res && res->hash_code == node->hash_code && res->key == node->key)
			return res;
		node->next = mk_node (get_node (res), 0);
		if (atomic_compare_and_swap (prev, mk_node (get_node (res), 0), mk_node (node, 0)))
			return node;
	}
}

static mark_ptr_t
list_delete (mark_ptr_t *head, key_t key, hash_t hash_code)
{
	mark_ptr_t res, *prev, next;
	while (1) {
		res = list_find (head, key, hash_code, &prev);
		if (!res || res->hash_code != hash_code || res->key != key)
			return NULL;
		next = atomic_load (&get_node (res)->next);
		if (!atomic_compare_and_swap (&get_node (res)->next, mk_node (get_node (next), 0), mk_node (get_node (next), 1)))
			continue;
		if (atomic_compare_and_swap (prev, mk_node (get_node (res), 0), mk_node (get_node (next), 0)))
			delete_node (get_node (res));
		else
			list_find (head, key, hash_code, &prev);
		return res;
	}
}

static void
dump_hash (conc_hashtable_t *ht)
{
	int i;
	node_t *cur = ht->table [0];
	printf ("---------\n");
	for (i = 0; i < ht->size; ++i)
		if (ht->table [i]) printf ("root [%d] -> %p\n", i, ht->table [i]);
	while (cur) {
		printf ("node %p hash %08x key %p\n", cur, cur->hash_code, (void*)(uintptr_t)cur->key);
		cur = cur->next;
	}
	printf ("---------\n");
}

static unsigned
get_parent (unsigned b)
{
	int i;
	for (i = 31; i >= 0; --i) {
		if (b & (1 << i))
			return b & ~(1 << i);
	}
	return 0;
}

static void
initialize_bucket (conc_hashtable_t *ht, mark_ptr_t *table, unsigned bucket)
{
	mark_ptr_t res;
	unsigned parent = get_parent (bucket);
	if (atomic_load (&table [parent]) == UNINITIALIZED)
		initialize_bucket (ht, table, parent);

	node_t *node = calloc (sizeof (node_t), 1);
	node->key = (key_t)(uintptr_t)bucket;
	node->hash_code = hash_dummy_key (bucket);

	res = list_insert (&table [parent], node);
	if (get_node (res) != node) {
		free (node);
		node = get_node (res);
	}

	atomic_store (&table [bucket], mk_node (node, 0));
}

static void
resize_table (conc_hashtable_t *ht, unsigned size)
{
	node_t **old_table = ht->table;
	node_t **new_table = calloc (sizeof (node_t*), size * 2);
	memcpy (new_table, old_table, sizeof (node_t*) * size);
	if (!atomic_compare_and_swap (&ht->size, size, size * 2)) {
		free (new_table);
		return;
	}
	if (!atomic_compare_and_swap ((void**)&ht->table, old_table, new_table))
		free (new_table);
}

boolean
conc_hashtable_insert (conc_hashtable_t *ht, key_t key, value_t value)
{
	hash_t hash = hash_key (key);
	node_t *node = calloc (sizeof (node_t), 1);
	mark_ptr_t *table = atomic_load (&ht->table);

	node->hash_code = hash_regular_key (hash);
	node->key = key;
	node->value = value;

	unsigned bucket = hash % ht->size;

	if (table [bucket] == UNINITIALIZED)
		initialize_bucket (ht, table, bucket);
	if (get_node (list_insert (&table [bucket], node)) != node) {
		free (node);
		return FALSE;
	}

	float size = (float)ht->size;
	if (atomic_fetch_and_inc (&ht->count) / size > LOAD_FACTOR)
		resize_table (ht, size);

	return TRUE;
}

value_t
conc_hashtable_find (conc_hashtable_t *ht, key_t key)
{
	mark_ptr_t res, *prev;
	hash_t hash = hash_key (key);
	unsigned bucket = hash % ht->size;
	mark_ptr_t *table = atomic_load (&ht->table);

	if (table [bucket] == UNINITIALIZED)
		initialize_bucket (ht, table, bucket);

	hash = hash_regular_key (hash);
	res = list_find (&ht->table [bucket], key, hash, &prev);
	if (res && get_node (res)->hash_code == hash && get_node (res)->key == key)
		return get_node (res)->value;
	return NULL;
}

value_t
conc_hashtable_delete (conc_hashtable_t *ht, key_t key)
{
	mark_ptr_t res;
	hash_t hash = hash_key (key);
	unsigned bucket = hash % ht->size;
	mark_ptr_t *table = atomic_load (&ht->table);

	if (table [bucket] == UNINITIALIZED)
		initialize_bucket (ht, table, bucket);

	hash = hash_regular_key (hash);
	res = list_delete (&ht->table [bucket], key, hash);
	if (!res)
		return NULL;

	atomic_fetch_and_dec (&ht->count);
	return get_node (res)->value;
}

conc_hashtable_t*
conc_hashtable_create (void)
{
	conc_hashtable_t *res = calloc (sizeof (conc_hashtable_t), 1);
	res->size = 16;
	res->table = calloc (sizeof (node_t), 16);
	res->table [0] = calloc (sizeof (node_t), 1);
	res->table [0]->hash_code = hash_dummy_key (0);
	res->table [0]->key = (key_t)(uintptr_t)0;
	return res;
}

static conc_hashtable_t *_ht;

#define INSERT_CNT 1000000
static void*
async_insert (key_t arg)
{
	int base = INSERT_CNT * (int)(intptr_t)arg;
	int i;
	for (i = 0; i < INSERT_CNT; ++i) {
		conc_hashtable_insert (_ht, UINT_TO_PTR (base + i), UINT_TO_PTR (1));
		conc_hashtable_insert (_ht, UINT_TO_PTR (base + i - INSERT_CNT), UINT_TO_PTR (2));
	}
	return NULL;
}

int main ()
{
	int i = 0;
/*	_ht = create ();
	pthread_t threads[4];

	for (i = 0; i < 4; ++i)
		pthread_create (&threads [i], NULL, async_insert, (void*)(intptr_t)i);

	for (i = 0; i < 4; ++i)
		pthread_join (threads [i], NULL);

	printf ("elements in %d\n", _ht->count);*/
	
	conc_hashtable_t *ht = conc_hashtable_create ();

	printf ("find %p %p %p\n", 
		conc_hashtable_find (ht, UINT_TO_PTR (0)),
		conc_hashtable_find (ht, UINT_TO_PTR (10)),
		conc_hashtable_find (ht, UINT_TO_PTR (26)));

	conc_hashtable_insert (ht, UINT_TO_PTR (0), UINT_TO_PTR (0x20));
	conc_hashtable_insert (ht, UINT_TO_PTR (26), UINT_TO_PTR (0x30));

	printf ("find %p %p %p\n", 
		conc_hashtable_find (ht, UINT_TO_PTR (0)),
		conc_hashtable_find (ht, UINT_TO_PTR (10)),
		conc_hashtable_find (ht, UINT_TO_PTR (26)));

	conc_hashtable_delete (ht, UINT_TO_PTR (0));

	printf ("find %p %p %p\n", 
		conc_hashtable_find (ht, UINT_TO_PTR (0)),
		conc_hashtable_find (ht, UINT_TO_PTR (10)),
		conc_hashtable_find (ht, UINT_TO_PTR (26)));
	
	printf ("%d ", conc_hashtable_insert (ht, UINT_TO_PTR (5), UINT_TO_PTR (0x10)));
	printf ("%d ", conc_hashtable_insert (ht, UINT_TO_PTR (5), UINT_TO_PTR (0x10)));
	printf ("%d ", conc_hashtable_insert (ht, UINT_TO_PTR (5), UINT_TO_PTR (0x10)));
	printf ("%d\n", ht->count);

	return 0;
}