#import bitset.c
#import os/self
#import strbuilder
#import tokenizer

#define TODOSIZE 100
#define TODOVOIDPSIZE 64

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

enum {
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

// Scope is a list of name->value bindings.
pub typedef {
	size_t size;
	char names[TODOSIZE][TODOSIZE];
	val_t *vals[TODOSIZE];
} scope_t;

bool GCDEBUG = false;

// Creates a new instance of the interpreter.
pub vm_t *new(size_t N) {
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

	// Scope 0 for globals.
	r->stack[r->depth++] = newscope();

	// These are special symbols used in compiled bodies for tail recursion.
	// They are stashed here in globals to keep them from being GC'd.
	evalstr(r, "(define __end __op_end)");
	evalstr(r, "(define __test_and_jump_if_false __op_test_and_jump_if_false)");

	// Scope 1 for predefined things.
	r->stack[r->depth++] = newscope();

	// Define standard functions.
	evalstr(r, "
(define (inc x) (+ 1 x))
(define (dec x) (- x 1))

(define (floor-iter x n)
    (if (> (inc n) x) n (floor-iter x (inc n))))

(define (floor x)
    (if (> x 0)
        (floor-iter x 0)
        (- (inc (floor (- x))))))

(define (ceil x) (+ 1 (floor x)))

(define (square x) (* x x))

(define (abs x) (if (> x 0) x (- x)))

(define (remainder x n) (- x (* n (floor (/ x n)))))

(define (even? n) (= (remainder n 2) 0))
");

	// A clean scope on top for user programs.
	r->stack[r->depth++] = newscope();
	return r;
}

// Frees an instance of the interpreter.
pub void free(vm_t *r) {
	// Ignore all the rest for now.
	OS.free(r);
}

// Creates a new scope.
scope_t *newscope() {
	scope_t *s = calloc(1, sizeof(scope_t));
	if (!s) panic("calloc failed");
	return s;
}

// Adds a binding to the scope.
void pushdef(scope_t *s, const char *name, val_t *val) {
	if (!name || !val) {
		panic("name or val is NULL");
	}
	if (s->size == TODOSIZE) {
		panic("no more space in scope");
	}
	strcpy(s->names[s->size], name);
	s->vals[s->size] = val;
	s->size++;
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

val_t *lookup(vm_t *inter, const char *n) {
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

// Parses a string into expressions and evaluates them.
pub val_t *evalstr(vm_t *inter, const char *s) {
	tokenizer.t *b = tokenizer.from_str(s);
	val_t **all = readall(inter, b);
	tokenizer.free(b);

	val_t *r = NULL;
	size_t n = 0;
	val_t *x = all[n++];
	while (x) {
		r = eval(inter, x);
		x = all[n++];
	}
	return r;
}

// Evaluates a node.
pub val_t *eval(vm_t *inter, val_t *x) {
	if (!x) {
		panic("eval of NULL");
	}
	switch (x->type) {
		case NUMBER: {
			return x;
		}
		case SYMBOL: {
			// Look up the symbol.
			// If it's defined, use the definition.
			// If not, keep the symbol as is.
			val_t *r = x;
			val_t *d = lookup(inter, x->name);
			if (d) r = d;
			trace_symbol_eval(inter, x, r);
			return r;
		}
		case LIST: {
			trace_list_before(inter, x);
			val_t *r = eval_list(inter, x);
			trace_list_after(inter, r);
			return r;
		}
		case FUNC: {
			return x;
		}
		default: {
			panic("unexpected value type");
		}
	}
}

// Evaluates a list node.
val_t *eval_list(vm_t *inter, val_t *x) {
	// The first item could be anything, we might need to evaluate it
	// to find out which function to run.
	val_t *first = car(x);
	if (first->type == LIST) {
		first = eval(inter, first);
	}
	// At this point we should have a symbol.
	if (first->type != SYMBOL) {
		char buf[TODOSIZE];
		print(first, buf, TODOSIZE);
		panic("invalid function invocation: got %s as function", buf);
	}
	return runfunc(inter, first->name, cdr(inter, x));
}

// Runs a function.
val_t *runfunc(vm_t *inter, const char *name, val_t *args) {
	if (inter->trace) {
		trace_indent(inter->depth);
		printf("RUN_FUNC: %s\n", name);
	}

	// See if there is a defined function with this name.
	// Custom definitions take precedence over the built-ins below.
	val_t *f = lookup(inter, name);
	if (f) {
		return runcustomfunc(inter, f, args);
	}

	switch str (name) {
		case "quote": { return car(args); }
		case "cons": { return cons(inter, args); }

		case "apply": { return apply(inter, args); }
		case "eq?": { return eq(inter, args); }
		case "define": { return fn_define(inter, args); }
		case "*": { return mul(inter, args); }
		case "+": { return add(inter, args); }
		case "-": { return sub(inter, args); }
		case "/": { return over(inter, args); }
		case ">": { return gt(inter, args); }
		case "<": { return lt(inter, args); }
		case "=": { return numeq(inter, args); }
		case "cond": { return cond(inter, args); }
		case "if": { return fif(inter, args); }
		case "and": { return and(inter, args); }
		case "or": { return or(inter, args); }
		case "not": { return not(inter, args); }
		case "__globalset": { return fn_globalset(inter, args); }
		case "__globalget": { return fn_globalget(inter, args); }
	}
	panic("unknown function: %s", name);
}

val_t *fn_globalset(vm_t *inter, val_t *args) {
	val_t *name = args->items[0];
	val_t *val = eval(inter, args->items[1]);
	pushdef(inter->stack[0], name->name, val);
	return NULL;
}

val_t *fn_globalget(vm_t *inter, val_t *args) {
	val_t *name = args->items[0];
	return globalget(inter, name->name);
}

val_t *globalget(vm_t *inter, const char *name) {
	return getdef(inter->stack[0], name);
}

val_t *runcustomfunc(vm_t *inter, val_t *f, val_t *args) {
	if (f->type != FUNC) {
		panic("not a function");
	}

	// Check the arguments number.
	size_t nargs = 0;
	if (args) nargs = args->nitems;
	if (nargs != f->fn_nargs) {
		panic("function expects %u arguments, got %zu", f->fn_nargs, nargs);
	}

	// Create a new scope for the call.
	scope_t *s2 = newscope();
	for (size_t i = 0; i < f->fn_nargs; i++) {
		pushdef(s2, f->fn_argnames[i], eval(inter, args->items[i]));
	}
	inter->stack[inter->depth++] = s2;

	// The result of execution will be set here.
	val_t *r = NULL;

	// Reformat the function body to have a better handle on execution
	// and execute each statement.
	val_t **body = compile(inter, f->fn_statements, f->fn_nstatements);
	for (int i = 0; i < TODOSIZE; i++) {
		val_t *x = body[i];

		// No more statements or a special end marker.
		if (!x || is_symbol(x, "__op_end")) {
			break;
		}

		// Conditional jump
		// (__op_test_and_jump_if_false pred)
		if (islist(x, "__op_test_and_jump_if_false")) {
			if (!eval(inter, x->items[1])) {
				i += 2; // ok expression + end
			}
			continue;
		}

		// if (islist(x, f->name)) {
		// 	// Build a new scope such that an honest call would produce.
		// 	scope_t *s3 = newscope();
		// 	for (size_t a = 0; a < f->nargs; a++) {
		// 		pushdef(s3, f->argnames[a], eval(inter, x->items[1+a]));
		// 	}

		// 	// Replace the scope and loop back to the beginning.
		// 	inter->stack[inter->depth-1] = s3;
		// 	r = NULL;
		// 	i = -1;
		// 	if (inter->trace) {
		// 		trace_indent(inter->depth);
		// 		printf("TAIL_RECUR: %s\n", f->name);
		// 	}
		// 	continue;
		// }

		r = eval(inter, x);
	}

	inter->depth--;
	OS.free(body);
	return r;
}

val_t *first(val_t *x) {
	return x->items[0];
}

val_t *second(val_t *x) {
	return x->items[1];
}

val_t *slice(vm_t *inter, val_t *x, size_t start) {
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

size_t len(val_t *x) {
	if (!x) panic("x is null");
	if (x->type != LIST) panic("not a list");
	return x->nitems;
}

// (define x const) defines a constant.
// (define (f x) body) defines a function.
val_t *fn_define(vm_t *inter, val_t *args) {
	val_t *name = first(args);
	scope_t *s = inter->stack[inter->depth-1];

	// (define x const)
	if (name->type == SYMBOL) {
		if (len(args) != 2) {
			panic("constant define requires 2 args, got %zu", len(args));
		}
		val_t *val = second(args);
		pushdef(s, name->name, eval(inter, val));
		return NULL;
	}

	// (define (twice x) (print x) (foo) (* x 2))
	if (name->type == LIST) {
		const char *fnname = name->items[0]->name;
		val_t *defargs = slice(inter, name, 1);
		val_t *defbody = slice(inter, args, 1);
		pushdef(s, fnname, newfunc(inter, defargs, defbody));
		return NULL;
	}

	dbgprint(args);
	panic("unknown define shape");
}


val_t *cond(vm_t *inter, val_t *args) {
	val_t *l = args;
	while (l) {
		val_t *cas = car(l);
		val_t *cond = car(cas);
		if (eval(inter, cond)) {
			val_t *result = car(cdr(inter, cas));
			return eval(inter, result);
		}
		l = cdr(inter, l);
	}
	return NULL;
}

// (not x) returns NULL if x is not null.
val_t *not(vm_t *inter, val_t *args) {
	if (eval(inter, car(args))) {
		return NULL;
	}
	return newsym(inter, "true");
}

// (if x then)
// (if x then else)
val_t *fif(vm_t *inter, val_t *args) {
	val_t *pred = car(args);
	val_t *ethen = car(cdr(inter, args));
	if (eval(inter, pred)) {
		return eval(inter, ethen);
	}
	if (args->nitems < 3) {
		return NULL;
	}
	val_t *eelse = car(cdr(inter, cdr(inter, args)));
	return eval(inter, eelse);
}

// (and a b c) returns c if a, b and c are not null.
// Returns null otherwise.
val_t *and(vm_t *inter, val_t *args) {
	for (size_t i = 0; i < args->nitems; i++) {
		if (!eval(inter, args->items[i])) {
			return NULL;
		}
	}
	return newsym(inter, "true");
}

// (or a b c) returns the first non-null argument or null.
val_t *or(vm_t *inter, val_t *args) {
	for (size_t i = 0; i < args->nitems; i++) {
		if (eval(inter, args->items[i])) {
			return newsym(inter, "true");
		}
	}
	return NULL;
}

val_t *apply(vm_t *inter, val_t *list) {
	val_t *fn = car(list);
	if (fn->type != SYMBOL) {
		dbgprint(list);
		panic("first element is a non-symbol");
	}
	return runfunc(inter, fn->name, eval(inter, car(cdr(inter, list))));
}

void printnum(char *buf, double x) {
	sprintf(buf, "%g", x);
}

double reduce(vm_t *inter, val_t *args, double start, int op) {
	if (args->type != LIST) {
		panic("not a list");
	}
	if (args->nitems < 2) {
		panic("want 2 or more arguments");
	}
	double r = start;
	for (size_t i = 0; i < args->nitems; i++) {
		val_t *x = eval(inter, args->items[i]);
		if (x->type != NUMBER) {
			panic("not a number");
		}
		double next = atof(x->value);
		switch (op) {
			case 1: { r *= next; }
			case 2: { r += next; }
			default: { panic("unknown op"); }
		}
	}
	return r;
}

// (* a b) returns a * b
val_t *mul(vm_t *inter, val_t *args) {
	char buf[100];
	printnum(buf, reduce(inter, args, 1, 1));
	return newnumber(inter, buf);
}

// (+ a b) returns a + b
val_t *add(vm_t *inter, val_t *args) {
	char buf[100];
	printnum(buf, reduce(inter, args, 0, 2));
	return newnumber(inter, buf);
}

// (- a b) returns a - b
val_t *sub(vm_t *inter, val_t *args) {
	char buf[100];

	val_t *a = eval(inter, car(args));
	if (args->nitems == 1) {
		printnum(buf, -atof(a->value));
		return newnumber(inter, buf);
	}
	val_t *b = eval(inter, car(cdr(inter, args)));
	if (a->type != NUMBER || b->type != NUMBER) {
		panic("not a number");
	}
	printnum(buf, atof(a->value) - atof(b->value));
	return newnumber(inter, buf);
}

// (/ a b) returns a / b
val_t *over(vm_t *inter, val_t *args) {
	val_t *a = eval(inter, car(args));
	val_t *b = eval(inter, car(cdr(inter, args)));
	if (a->type != NUMBER || b->type != NUMBER) {
		dbgprint(args);
		panic("/: an argument is not a number");
	}
	char buf[100];
	printnum(buf, atof(a->value) / atof(b->value));
	return newnumber(inter, buf);
}

val_t *numeq(vm_t *inter, val_t *args) {
	val_t *a = eval(inter, car(args));
	val_t *b = eval(inter, car(cdr(inter, args)));
	if (atof(a->value) == atof(b->value)) {
		return newsym(inter, "true");
	}
	return NULL;
}

// (eq? a b) returns true if a equals b.
val_t *eq(vm_t *inter, val_t *args) {
	val_t *a = eval(inter, car(args));
	val_t *b = eval(inter, car(cdr(inter, args)));

	// If types don't match, then not equal.
	if (a->type != b->type) {
		return NULL;
	}
	bool same = false;
	switch (a->type) {
		case SYMBOL: { same = !strcmp(a->name, b->name); }
		case NUMBER: { same = !strcmp(a->value, b->value); }
		default: {
			panic("unhandled item type: %d", a->type);
		}
	}
	if (same) {
		return newsym(inter, "true");
	}
	return NULL;
}

// (> a b) returns true if a > b
val_t *gt(vm_t *inter, val_t *args) {
	val_t *a = eval(inter, car(args));
	val_t *b = eval(inter, car(cdr(inter, args)));
	if (atof(a->value) > atof(b->value)) {
		return newsym(inter, "true");
	}
	return NULL;
}

// (< a b) returns true if a < b
val_t *lt(vm_t *inter, val_t *args) {
	val_t *a = eval(inter, car(args));
	val_t *b = eval(inter, car(cdr(inter, args)));
	if (atof(a->value) < atof(b->value)) {
		return newsym(inter, "true");
	}
	return NULL;
}

// (cons 1 x) constructs a list (1, ...x)
val_t *cons(vm_t *inter, val_t *args) {
	val_t *head = car(args);
	val_t *tail = car(cdr(inter, args));

	val_t *r = newlist(inter);
	r->items[r->nitems++] = head;
	for (size_t i = 0; i < tail->nitems; i++) {
		r->items[r->nitems++] = tail->items[i];
	}
	return r;
}

// Returns the first item of the list x.
val_t *car(val_t *x) {
	if (x->type != LIST || x->nitems == 0) {
		return NULL;
	}
	return x->items[0];
}

// Returns the tail of the list x.
val_t *cdr(vm_t *inter, val_t *x) {
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

void trace_indent(size_t depth) {
	for (size_t i = 0; i < depth; i++) printf("  ");
}

void trace_symbol_eval(vm_t *inter, val_t *x, *r) {
	if (!inter->trace) return;
	trace_indent(inter->depth);
	printf("EVAL_SYM %s: ", x->name);
	dbgprint(r);
}

void trace_list_before(vm_t *inter, val_t *x) {
	if (!inter->trace) return;
	trace_defs(inter);
	trace_indent(inter->depth);
	printf("eval: ");
	dbgprint(x);
}

void print_scope(scope_t *s) {
	for (size_t i = 0; i < s->size; i++) {
		printf("[%zu] %s = ", i, s->names[i]);
		dbgprint(s->vals[i]);
	}
	puts("---");
}

void trace_defs(vm_t *inter) {
	// -1 to exclude the first scope where built-in definitions are.
	for (size_t d = 0; d < inter->depth - 1; d++) {
		scope_t *s = inter->stack[inter->depth - d - 1];
		print_scope(s);
	}
}

void trace_list_after(vm_t *inter, val_t *r) {
	if (!inter->trace) return;
	trace_indent(inter->depth);
	printf("result: ");
	dbgprint(r);
}

pub val_t **readall(vm_t *p, tokenizer.t *b) {
	val_t **all = calloc(100, sizeof(b));
	size_t n = 0;
	while (true) {
		val_t *t = readtok(p, b);
		if (!t) break;
		all[n++] = t;
	}
	return all;
}

// Reads next item from the buffer.
pub val_t *readtok(vm_t *p, tokenizer.t *b) {
	tokenizer.spaces(b);
	if (!tokenizer.more(b)) {
		return NULL;
	}
	if (tokenizer.peek(b) == '(') {
		return readlist(p, b);
	}
	if (isdigit(tokenizer.peek(b))) {
		return readnum(p, b);
	}
	return readsymbol(p, b);
}

// Reads a number.
val_t *readnum(vm_t *p, tokenizer.t *b) {
	char buf[100];
	if (!tokenizer.num(b, buf, 100)) {
		panic("failed to read a number");
	}
	return newnumber(p, buf);
}

// Reads a symbol.
val_t *readsymbol(vm_t *p, tokenizer.t *b) {
	val_t *x = newsym(p, "");
	int pos = 0;
	while (tokenizer.more(b) && !isspace(tokenizer.peek(b)) && tokenizer.peek(b) != ')') {
		x->name[pos++] = tokenizer.get(b);
	}
	if (pos == 0) {
		panic("failed to read symbol at %s", tokenizer.posstr(b));
	}
	return x;
}


// Reads a list.
val_t *readlist(vm_t *p, tokenizer.t *b) {
	val_t *x = newlist(p);

	tokenizer.get(b); // "("
	tokenizer.spaces(b);
	while (tokenizer.peek(b) != EOF && tokenizer.peek(b) != ')') {
		x->items[x->nitems++] = readtok(p, b);
		tokenizer.spaces(b);
	}
	if (tokenizer.peek(b) != ')') {
		panic("expected )");
	}
	tokenizer.get(b); // ")"
	return x;
}

void gc_trace(const char *format, ...) {
	if (!GCDEBUG) return;

	va_list args = {};
	va_start(args, format);
	vprintf(format, args);
	va_end(args);
	putchar('\n');
}

val_t *newnumber(vm_t *p, const char *val) {
	val_t *x = make(p);
	x->type = NUMBER;
	x->value = calloc(60, 1);
	strcpy(x->value, val);
	return x;
}

val_t *newlist(vm_t *p) {
	val_t *x = make(p);
	x->type = LIST;
	x->items = calloc(10, sizeof(x));
	return x;
}

val_t *newsym(vm_t *p, const char *s) {
	val_t *x = make(p);
	x->type = SYMBOL;
	x->name = calloc(60, 1);
	strcpy(x->name, s);
	return x;
}

// Creates a function with given args and body.
// Both args and body must be lists.
val_t *newfunc(vm_t *inter, val_t *args, val_t *body) {
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

// Runs a full GC cycle.
pub void gc(vm_t *inter) {
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

pub bool islist(val_t *x, const char *name) {
	return x->type == LIST
		&& x->items[0]->type == SYMBOL
		&& !strcmp(x->items[0]->name, name);
}

bool is_symbol(val_t *x, const char *name) {
	return x->type == SYMBOL && !strcmp(x->name, name);
}

// Prints the given item to stdout for debugging.
void dbgprint(val_t *x) {
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

val_t **compile(vm_t *p, val_t **in, size_t n) {
	val_t **out = calloc(TODOSIZE, TODOVOIDPSIZE);
	int pos = 0;

	for (size_t i = 0; i < n; i++) {
		val_t *x = in[i];

		// Flatten tail ifs so the interpreter can attempt a tail recursion.
		if (i == n - 1 && islist(x, "if")) {
			pos = compile_if(p, x, out, pos);
			continue;
		}
		if (i == n - 1 && islist(x, "cond")) {
			pos = compile_cond(p, x, out, pos);
			continue;
		}
		out[pos++] = x;
	}

	return out;
}

int compile_if(vm_t *p, val_t *x, val_t *body[], int added) {
	// Tests the condition and skips the ok branch if false.
	val_t *tst = newlist(p);
	tst->items[tst->nitems++] = globalget(p, "__test_and_jump_if_false");
	tst->items[tst->nitems++] = x->items[1];
	body[added++] = tst;

	// The ok branch with an end marker.
	body[added++] = x->items[2];
	body[added++] = globalget(p, "__end");

	// The else branch.
	body[added++] = x->items[3];

	return added;
}

int compile_cond(vm_t *p, val_t *cond, val_t *body[], int added) {
	for (size_t i = 1; i < cond->nitems; i++) {
		val_t *alt = cond->items[i];

		// Tests the condtion and skips the ok expression if false.
		// Implies that cond values have exactly one expression.
		val_t *tst = newlist(p);
		tst->items[tst->nitems++] = globalget(p, "__test_and_jump_if_false");
		tst->items[tst->nitems++] = alt->items[0];
		body[added++] = tst;

		// Value followed by the stop command
		// (implies that this cond is the last expression)
		body[added++] = alt->items[1];
		body[added++] = globalget(p, "__end");
	}
	return added;
}
