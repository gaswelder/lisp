#import os/self

#define TODOSIZE 100

// An instance of the interpreter, with all its internal state.
pub typedef {
	bool trace;

	scope_t *stack[400];
	size_t depth;

	bool *in_use;
	size_t poolsize;
	val_t *poolitems;
	size_t last_alloc;
} vm_t;

// Scope is a list of name->value bindings.
pub typedef {
	size_t size;
	char names[TODOSIZE][TODOSIZE];
	val_t *vals[TODOSIZE];
} scope_t;

pub enum {
	LIST = 1,
	SYMBOL,
	NUMBER,
	FUNC,
};

pub typedef {
	size_t mempos; // where in the pool this value is located

	int type;

	// for number:
	char *value;

	// for symbol:
	char *name;

	// for list:
	val_t **items;
	uint8_t nitems;

	// for func:
	uint8_t fn_nargs;
	char fn_argnames[10][10];
	uint8_t fn_nstatements;
	val_t *fn_statements[TODOSIZE];
} val_t;

pub vm_t *newvm(size_t N) {
	vm_t *r = calloc(1, sizeof(vm_t));
	if (!r) panic("calloc failed");

	// Enable tracing output if requested.
	const char *v = self.getenv("DEBUG");
	if (v && strcmp(v, "0")) {
		r->trace = true;
	}

	// Memory.
	r->poolitems = calloc(N, sizeof(val_t));
	r->poolsize = N;
	r->in_use = calloc(N, sizeof(bool));

	return r;
}