#include <stdio.h>
#include <stdlib.h>

#define TERM_LAMBDA 1
#define TERM_APPLICATION 2
#define TERM_REFERENCE 3

struct term {
	int tag;
	union {
		struct {
			int index;
		} lambda;
		struct {
			struct term *function;
			struct term *argument;
		} application;

		struct {
			int sort;
			void *pointer;
		} reference;
	} as;

	struct term *next;
};

struct constructor {
	int number_of_arguments;
	struct term *argument_types;
};
struct indexed_algebraic_data_type {
	int tag;

	int number_of_parameters;
	int number_of_indices;

	int number_of_constructors;
	struct constructor *constructors;
};

struct match {
	struct term *type;
	struct term *cases;
};

#define DATA_TYPE_OBJECT_SORT_TYPE_CONSTRUCTOR 0
#define DATA_TYPE_OBJECT_SORT_ELEMENT_CONSTRUCTOR 1

struct data_type_object {
	struct indexed_algebraic_data_type *type;

	int sort;
};

struct indexed_algebraic_data_type natural_number;
int setup_natural_number()
{
	natural_number.number_of_parameters = 0;
	natural_number.number_of_indices = 0;

	natural_number.number_of_constructors = 2;
	natural_number.constructors = calloc(2, sizeof(struct constructor));

	/* zero */
	natural_number.constructors[0].number_of_arguments = 0;
	natural_number.constructors[0].argument_types = NULL;

	/* succ */
	natural_number.constructors[1].number_of_arguments = 1;
	natural_number.constructors[1].argument_types = calloc(1, sizeof(struct term));
	natural_number.constructors[1].argument_types[0].tag = TERM_IADT;
	natural_number.constructors[1].argument_types[0].as.type_system.sort = -1;
	natural_number.constructors[1].argument_types[0].as.type_system.p_iadt = &natural_number;
}

#define MAX_ARENA 256
struct term term_arena[MAX_ARENA];
int term_upfront;

#define HASH_TABLE_SIZE 32
struct term *term_hash_table[HASH_TABLE_SIZE];

#if 0
int print_hash_table()
{
	int i;

	for(i = 0; i < HASH_TABLE_SIZE; ++i) {
		struct term *temp;

		printf("%d:\n", i);
		temp = term_hash_table[i];
		while(temp != NULL) {
			printf("\t%x", temp);
			temp = temp->next;
		}
	}
}
#endif
int hash_term(struct term *t);
int hash_term_lambda(
	int x)
{
	return x;
}
int hash_term_application(
	struct term *function,
	struct term *argument)
{
	return hash_term(function) + hash_term(argument);
}
int hash_term(struct term *t)
{
	int hash_value;

	hash_value = t->tag;

	switch(t->tag) {
	case TERM_LAMBDA:
		hash_value += hash_term_lambda(t->as.lambda.index);
		break;
	case TERM_APPLICATION:
		hash_value += hash_term_application(
			t->as.application.function,
			t->as.application.argument);
		break;
	}

	return hash_value;
}

int term_is_same_lambda(
	struct term *t,
	int index)
{
	if(t->tag != TERM_LAMBDA) {
		return 1;
	}
	if(t->as.lambda.index != index) {
		return 1;
	}
	return 0;
}
int term_is_same_application(
	struct term *t,
	struct term *function,
	struct term *argument)
{
	if(t->tag != TERM_APPLICATION) {
		return 1;
	}
	if(t->as.application.function != function) {
		return 1;
	}
	if(t->as.application.argument != argument) {
		return 1;
	}
	return 0;
}
struct term *term_introduce_lambda(int index)
{
	int hash_value;
	struct term **p_candidate;

	/* search existing term */
	hash_value = hash_term_lambda(index);
	printf("hash_value = %d\n", hash_value);
	p_candidate = &term_hash_table[hash_value];
	printf("*p_candidate = %x\n", *p_candidate);
	while(*p_candidate != NULL) {
		if(term_is_same_lambda(
			*p_candidate,
			index) == 0)
		{
			return *p_candidate;
		}
		p_candidate = &(*p_candidate)->next;
	}

	/* create new term as lambda */
	{
		struct term *candidate = &term_arena[term_upfront];

		candidate->tag = TERM_LAMBDA;
		candidate->as.lambda.index = index;
		candidate->next = term_hash_table[hash_value];
		term_hash_table[hash_value] = candidate;

		term_upfront++;
		return candidate;
	}

}
struct term *term_introduce_application(
	struct term *function,
	struct term *argument)
{
	int hash_value;
	struct term **p_candidate;

	/* search existing term */
	hash_value = hash_term_application(
		function,
		argument);
	p_candidate = &term_hash_table[hash_value];
	while(*p_candidate != NULL) {
		if(term_is_same_application(*p_candidate,
			function,
			argument) == 0)
		{
			return *p_candidate;
		}
		p_candidate = &(*p_candidate)->next;
	}

	/* create new term as lambda */
	{
		struct term *candidate = &term_arena[term_upfront];

		candidate->tag = TERM_APPLICATION;
		candidate->as.application.function = function;
		candidate->as.application.argument = argument;
		candidate->next = term_hash_table[hash_value];
		term_hash_table[hash_value] = candidate;

		term_upfront++;
		return candidate;
	}
}

#define POLARITY_VALUE 0x00
#define POLARITY_COMPUTATION 0x01

struct binding {
	struct term *term;
	struct term *type;
};
struct binding binding_arena[MAX_ARENA];
int binding_upfront;

/****************************************************************
 *
 ****************************************************************/

struct runtime_environment {
	struct term *term;
	struct runtime_environment *next;
};
struct runtime_environment env_arena[MAX_ARENA];
struct runtime_environment *env_pool;

int env_pool_discard(struct runtime_environment *env)
{
	env->next = env_pool;
	env_pool = env;
}

int env_pool_init()
{
	int i;

	env_pool = NULL;
	for(i = 0; i < MAX_ARENA; ++i) {
		env_pool_discard(&env_arena[i]);
	}
	return 0;
}

struct term *runtime_environment_evaluate_term(
	struct runtime_environment *env,
	struct term *t);
struct term *runtime_environment_evaluate_term_lambda(
	struct runtime_environment *env,
	int x)
{
	int i;
	struct runtime_environment *temp;

	temp = env;
	for(i = 0; i < x; ++i) {
		temp = temp->next;
	}
	return temp->term;
}
struct term *runtime_environment_evaluate_term_application(
	struct runtime_environment *env,
	struct term *function,
	struct term *argument)
{
	struct runtime_environment *temp_env;

	temp_env = env_pool;
	env_pool = env_pool->next;

	temp_env->term = argument;
	temp_env->next = env;

	return runtime_environment_evaluate_term(
		temp_env,
		function);
}
struct term *runtime_environment_evaluate_term(
	struct runtime_environment *env,
	struct term *t)
{
	switch(t->tag) {
	case TERM_LAMBDA:
		return runtime_environment_evaluate_term_lambda(
			env,
			t->as.lambda.index);
		break;
	case TERM_APPLICATION:
		return runtime_environment_evaluate_term_application(
			env,
			t->as.application.function,
			t->as.application.argument);
		break;
	}
}

/****************************************************************
 *
 ****************************************************************/

int main()
{
	struct term *term, *term0, *term1;

	printf("hello, world\n");
	env_pool_init();
	term_upfront = 0;
	binding_upfront = 0;

	term = term_introduce_lambda(0);
	printf("pointer = %x\n", term);
	term0 = term;

	term = term_introduce_lambda(1);
	printf("pointer = %x\n", term);
	term1 = term;

	term = term_introduce_application(term0, term1);
	printf("pointer = %x\n", term);
	{
		struct term *res;
		res = runtime_environment_evaluate_term(
			NULL,
			term);
		printf("result = %x\n", res);
	}

	binding_arena[binding_upfront].term = term_introduce_lambda(0);
//	binding_arena[binding_upfront].polarity = POLARITY_VALUE;
	binding_upfront++;
}
