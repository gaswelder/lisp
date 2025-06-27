#import os/self
#import bitset.c
#import strbuilder

#define TODOSIZE 100
bool GCDEBUG = false;

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

// Creates a new scope.
pub scope_t *newscope() {
	scope_t *s = calloc(1, sizeof(scope_t));
	if (!s) panic("calloc failed");
	return s;
}

// Adds a binding to the current scope.
pub void pushdef(vm_t *inter, const char *name, val_t *val) {
	if (!name || !val) {
		panic("name or val is NULL");
	}
    scope_t *s = inter->stack[inter->depth-1];
	if (s->size == TODOSIZE) {
		panic("no more space in scope");
	}
	strcpy(s->names[s->size], name);
	s->vals[s->size] = val;
	s->size++;
}

pub scope_t *pushscope(vm_t *inter) {
    if (inter->depth == 400) {
        panic("stack limit reached");
    }
    scope_t *s = newscope();
	inter->stack[inter->depth++] = s;
    return s;
}

pub void popscope(vm_t *inter) {
    if (inter->depth == 0) {
        panic("stack is empty");
    }
    inter->depth--;
    OS.free(inter->stack[inter->depth]);
}

// Returns the value bound to name n in scope s.
// Returns NULL if there is no such value.
val_t *getdef(scope_t *s, const char *n) {
	if (!n) {
		panic("n is null");
	}
	val_t *r = NULL;
	for (size_t i = 0; i < s->size; i++) {
		if (!strcmp(n, s->names[i])) {
			// Don't break because redefinitions can be added further down.
			r = s->vals[i];
		}
	}
	return r;
}

pub val_t *globalget(vm_t *inter, const char *name) {
	return getdef(inter->stack[0], name);
}

pub val_t *lookup(vm_t *inter, const char *n) {
	if (!n) {
		panic("n is null");
	}
	for (size_t d = 0; d < inter->depth; d++) {
		scope_t *s = inter->stack[inter->depth - 1 - d];
		val_t *r = getdef(s, n);
		if (r) {
			return r;
		}
	}
	return NULL;
}

// Returns the first item of the list x.
pub val_t *car(val_t *x) {
	if (x->type != LIST || x->nitems == 0) {
		return NULL;
	}
	return x->items[0];
}

// Returns the tail of the list x.
pub val_t *cdr(vm_t *inter, val_t *x) {
	if (!x || x->type != LIST || x->nitems <= 1) {
		return NULL;
	}
	val_t *r = newlist(inter);
	for (size_t i = 1; i < x->nitems; i++) {
		r->items[i-1] = x->items[i];
	}
	r->nitems = x->nitems-1;
	return r;
}

pub val_t *first(val_t *x) {
	return x->items[0];
}

pub val_t *second(val_t *x) {
	return x->items[1];
}

pub val_t *slice(vm_t *inter, val_t *x, size_t start) {
	if (x->type != LIST) {
		panic("expected a list");
	}
	val_t *r = newlist(inter);
	size_t n = len(x);
	for (size_t i = start; i < n; i++) {
		r->items[r->nitems++] = x->items[i];
	}
	return r;
}

pub val_t *newnumber(vm_t *p, const char *val) {
	val_t *x = make(p);
	x->type = NUMBER;
	x->value = calloc(TODOSIZE, 1);
	strcpy(x->value, val);
	return x;
}

pub val_t *newlist(vm_t *p) {
	val_t *x = make(p);
	x->type = LIST;
	x->items = calloc(TODOSIZE, sizeof(x));
	return x;
}

pub val_t *newsym(vm_t *p, const char *s) {
	val_t *x = make(p);
	x->type = SYMBOL;
	x->name = calloc(TODOSIZE, 1);
	strcpy(x->name, s);
	return x;
}

// Creates a function with given args and body.
// Both args and body must be lists.
pub val_t *newfunc(vm_t *inter, val_t *args, val_t *body) {
	val_t *x = make(inter);
	x->type = FUNC;
	for (size_t i = 0; i < args->nitems; i++) {
		strcpy(x->fn_argnames[x->fn_nargs++], args->items[i]->name);
	}
	for (size_t i = 0; i < body->nitems; i++) {
		x->fn_statements[x->fn_nstatements++] = body->items[i];
	}
	return x;
}

val_t *make(vm_t *p) {
	val_t *x = alloc(p);
	if (!x) {
		gc(p);
		x = alloc(p);
		if (!x) {
			panic("out of memory");
		}
	}
	return x;
}

// Returns a pointer to an unused value from the pool.
// Returns NULL if there are no free values.
val_t *alloc(vm_t *inter) {
	for (size_t i = 0; i < inter->poolsize; i++) {
		size_t pos = (inter->last_alloc + i) % inter->poolsize;
		if (inter->in_use[pos]) {
			continue;
		}
		gc_trace("alloc at %zu", pos);
		inter->in_use[pos] = true;
		inter->poolitems[pos].mempos = pos;
		inter->last_alloc = pos;
		return &inter->poolitems[pos];
	}
	gc_trace("OOM");
	return NULL;
}

void gc_trace(const char *format, ...) {
	if (!GCDEBUG) return;

	va_list args = {};
	va_start(args, format);
	vprintf(format, args);
	va_end(args);
	putchar('\n');
}

// Runs a full GC cycle.
void gc(vm_t *inter) {
	gc_trace("gc start: depth=%zu, poolsize=%zu", inter->depth, inter->poolsize);

	bitset.t *used = bitset.new(inter->poolsize);

	for (size_t i = 0; i < inter->depth; i++) {
		gc_trace("frame %zu\n-----------", i);
		scope_t *s = inter->stack[i];
		for (size_t j = 0; j < s->size; j++) {
			val_t *b = s->vals[j];
			gc_trace("%zu: %s", j, s->names[j]);
			gc_mark(used, inter, b);
		}
	}

	size_t frees = 0;
	for (size_t i = 0; i < inter->poolsize; i++) {
		if (!inter->in_use[i] || bitset.isset(used, i)) {
			continue;
		}
		if (GCDEBUG) {
			printf("free %zu: ", i);
			dbgprint(&inter->poolitems[i]);
		}
		inter->in_use[i] = false;
		// memset(&p->poolitems[i], 0, sizeof(val_t));
		frees++;
	}
	// printf("gc: %zu frees\n", frees);
	bitset.free(used);
}

void gc_mark(bitset.t *used, vm_t *inter, val_t *x) {
	if (!x) {
		return;
	}
	if (GCDEBUG) {
		printf("mark %zu: ", x->mempos);
		dbgprint(x);
	}
	bitset.set(used, x->mempos);
	if (x->type == LIST) {
		for (size_t i = 0; i < x->nitems; i++) {
			gc_mark(used, inter, x->items[i]);
		}
	}
	if (x->type == FUNC) {
		for (size_t i = 0; i < x->fn_nstatements; i++) {
			gc_mark(used, inter, x->fn_statements[i]);
		}
	}
}

pub size_t len(val_t *x) {
	if (!x) panic("x is null");
	if (x->type != LIST) panic("not a list");
	return x->nitems;
}

// Prints the given item to stdout for debugging.
pub void dbgprint(val_t *x) {
	char buf[4096];
	if (!x) {
		printf("NULL\n");
		return;
	}
	print(x, buf, 4096);
	printf("%s\n", buf);
}

// Prints the given node into the buf.
pub void print(val_t *x, char *buf, size_t len) {
	strbuilder.str *s = strbuilder.str_new();
	_print(s, x);
	char *r = strbuilder.str_unpack(s);
	strncpy(buf, r, len);
	OS.free(r);
}

// Prints a display representation of x into s.
void _print(strbuilder.str *s, val_t *x) {
	if (!x) {
		strbuilder.adds(s, "NULL");
		return;
	}
	switch (x->type) {
		case SYMBOL: {
			strbuilder.adds(s, x->name);
		}
		case NUMBER: {
			strbuilder.adds(s, x->value);
		}
		case LIST: {
			strbuilder.str_addc(s, '(');
			for (size_t i = 0; i < x->nitems; i++) {
				if (i > 0) {
					strbuilder.str_addc(s, ' ');
				}
				_print(s, x->items[i]);
			}
			strbuilder.str_addc(s, ')');
		}
		case FUNC: {
			strbuilder.adds(s, "fn (");
			for (size_t i = 0; i < x->fn_nargs; i++) {
				if (i > 0) strbuilder.adds(s, " ");
				strbuilder.adds(s, x->fn_argnames[i]);
			}
			strbuilder.adds(s, ") ...");
		}
		default: {
			panic("unknown type");
		}
	}
}
