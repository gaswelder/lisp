#import bitset.c
#import os/self
#import strbuilder
#import tokenizer

// An instance of the interpreter, with all its internal state.
pub typedef {
	bool trace;

	scope_t *stack[400];
	size_t depth;

	bool *in_use;
	size_t poolsize;
	tok_t *poolitems;
	size_t last_alloc;
} t;

// Represents a single binding.
pub typedef {
	bool isfunc;

	// Name of the function or constant.
	char name[80];

	// constant:
	tok_t *val;

	// function:
	size_t nargs;
	char argnames[10][10];
	size_t nvals;
	tok_t *vals[100];
} binding_t;

// Scope is a list of bindings, a call stack frame.
pub typedef {
	size_t size;
	binding_t defs[100];
} scope_t;

bool GCDEBUG = false;

// Creates a new instance of the interpreter.
pub t *new(size_t N) {
	t *r = calloc(1, sizeof(t));
	if (!r) panic("calloc failed");

	// Enable tracing output if requested.
	const char *v = self.getenv("DEBUG");
	if (v && strcmp(v, "0")) {
		r->trace = true;
	}

	// Memory.
	r->poolitems = calloc(N, sizeof(tok_t));
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
pub void free(t *r) {
	// Ignore all the rest for now.
	OS.free(r);
}

// Creates a new instance of scope.
scope_t *newscope() {
	scope_t *s = calloc(1, sizeof(scope_t));
	if (!s) panic("calloc failed");
	return s;
}

// Adds a binding to the scope.
void pushdef(scope_t *s, const char *name, tok_t *val) {
	if (s->size == 100) {
		panic("no more space in scope");
	}
	strcpy(s->defs[s->size].name, name);
	s->defs[s->size].val = val;
	s->size++;
}

binding_t *getdef(scope_t *s, const char *name) {
	if (!name) {
		return NULL;
	}
	binding_t *r = NULL;
	for (size_t i = 0; i < s->size; i++) {
		if (!strcmp(name, s->defs[i].name)) {
			// Don't break because redefinitions can be added further down.
			r = &s->defs[i];
		}
	}
	return r;
}

// Finds a binding.
binding_t *lookup(t *inter, const char *name) {
	for (size_t d = 0; d < inter->depth; d++) {
		scope_t *s = inter->stack[inter->depth - 1 - d];
		binding_t *r = getdef(s, name);
		if (r) {
			return r;
		}
	}
	return NULL;
}

// Parses a string into expressions and evaluates them.
pub tok_t *evalstr(t *inter, const char *s) {
	tokenizer.t *b = tokenizer.from_str(s);
	tok_t **all = readall(inter, b);
	tokenizer.free(b);

	tok_t *r = NULL;
	size_t n = 0;
	tok_t *x = all[n++];
	while (x) {
		r = eval(inter, x);
		x = all[n++];
	}
	return r;
}

// Evaluates a node.
pub tok_t *eval(t *inter, tok_t *x) {
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
			tok_t *r = x;
			binding_t *d = lookup(inter, x->name);
			if (d) r = d->val;
			trace_symbol_eval(inter, x, r);
			return r;
		}
		case LIST: {
			trace_list_before(inter, x);
			tok_t *r = eval_list(inter, x);
			trace_list_after(inter, r);
			return r;
		}
		default: {
			panic("unexpected value type");
		}
	}
}

// Evaluates a list node.
tok_t *eval_list(t *inter, tok_t *x) {
	// The first item could be anything, we might need to evaluate it
	// to find out which function to run.
	tok_t *first = car(x);
	if (first->type == LIST) {
		first = eval(inter, first);
	}
	// At this point we should have a symbol.
	if (first->type != SYMBOL) {
		char buf[100];
		print(first, buf, 100);
		panic("invalid function invocation: got %s as function", buf);
	}
	return runfunc(inter, first->name, cdr(inter, x));
}

// Runs a function.
tok_t *runfunc(t *inter, const char *name, tok_t *args) {
	if (inter->trace) {
		trace_indent(inter->depth);
		printf("RUN_FUNC: %s\n", name);
	}
	// See if there is a defined function with this name.
	// Custom definitions take precedence over the built-ins below.
	binding_t *f = lookup(inter, name);
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

tok_t *fn_globalset(t *inter, tok_t *args) {
	tok_t *name = args->items[0];
	tok_t *val = eval(inter, args->items[1]);
	pushdef(inter->stack[0], name->name, val);
	return NULL;
}

tok_t *fn_globalget(t *inter, tok_t *args) {
	tok_t *name = args->items[0];
	return globalget(inter, name->name);
}

tok_t *globalget(t *inter, const char *name) {
	binding_t *d = getdef(inter->stack[0], name);
	if (d) {
		return d->val;
	}
	return NULL;
}

tok_t *runcustomfunc(t *inter, binding_t *f, tok_t *args) {
	if (!f->isfunc) {
		panic("%s is not a function", f->name);
	}

	// Check the arguments number
	size_t nargs = 0;
	if (args) nargs = args->nitems;
	if (nargs != f->nargs) {
		panic("function expects %zu arguments, got %zu", f->nargs, nargs);
	}

	// Reformat the function body to have a better handle on execution.
	tok_t **body = compile(inter, f->vals, f->nvals);

	// Create a new scope for the call.
	scope_t *s2 = newscope();
	for (size_t i = 0; i < f->nargs; i++) {
		pushdef(s2, f->argnames[i], eval(inter, args->items[i]));
	}
	inter->stack[inter->depth++] = s2;

	tok_t *r = NULL;
	for (int i = 0; i < 100; i++) {
		tok_t *x = body[i];
		if (!x) break;
		if (x->type == SYMBOL && !strcmp(x->name, "__op_end")) {
			break;
		}
		if (islist(x, "__op_test_and_jump_if_false")) {
			if (!eval(inter, x->items[1])) {
				i += 2; // ok expression + end
			}
			continue;
		}

		if (islist(x, f->name)) {
			// Build a new scope such that an honest call would produce.
			scope_t *s3 = newscope();
			for (size_t a = 0; a < f->nargs; a++) {
				pushdef(s3, f->argnames[a], eval(inter, x->items[1+a]));
			}

			// Replace the scope and loop back to the beginning.
			inter->stack[inter->depth-1] = s3;
			r = NULL;
			i = -1;
			if (inter->trace) {
				trace_indent(inter->depth);
				printf("TAIL_RECUR: %s\n", f->name);
			}
			continue;
		}

		r = eval(inter, x);
	}

	inter->depth--;
	OS.free(body);
	return r;
}

// (define x const) defines a constant.
// (define (f x) body) defines a function.
tok_t *fn_define(t *inter, tok_t *args) {
	tok_t *def = car(args);

	// (define x const)
	if (def->type == SYMBOL) {
		tok_t *val = car(cdr(inter, args));
		scope_t *s = inter->stack[inter->depth-1];
		pushdef(s, def->name, eval(inter, val));
		return NULL;
	}

	// (define (twice x) (print x) (foo) (* x 2))
	if (def->type == LIST) {
		scope_t *s = inter->stack[inter->depth-1];
		binding_t *d = &s->defs[s->size++];
		strcpy(d->name, car(def)->name);
		d->isfunc = true;

		// Copy arguments
		for (size_t i = 1; i < def->nitems; i++) {
			strcpy(d->argnames[d->nargs++], def->items[i]->name);
		}

		// Copy body expressions
		for (size_t i = 1; i < args->nitems; i++) {
			d->vals[d->nvals++] = args->items[i];
		}

		return NULL;
	}

	dbgprint(args);
	panic("unknown define shape");
}


tok_t *cond(t *inter, tok_t *args) {
	tok_t *l = args;
	while (l) {
		tok_t *cas = car(l);
		tok_t *cond = car(cas);
		if (eval(inter, cond)) {
			tok_t *result = car(cdr(inter, cas));
			return eval(inter, result);
		}
		l = cdr(inter, l);
	}
	return NULL;
}

// (not x) returns NULL if x is not null.
tok_t *not(t *inter, tok_t *args) {
	if (eval(inter, car(args))) {
		return NULL;
	}
	return newsym(inter, "true");
}

// (if x then)
// (if x then else)
tok_t *fif(t *inter, tok_t *args) {
	tok_t *pred = car(args);
	tok_t *ethen = car(cdr(inter, args));
	if (eval(inter, pred)) {
		return eval(inter, ethen);
	}
	if (args->nitems < 3) {
		return NULL;
	}
	tok_t *eelse = car(cdr(inter, cdr(inter, args)));
	return eval(inter, eelse);
}

// (and a b c) returns c if a, b and c are not null.
// Returns null otherwise.
tok_t *and(t *inter, tok_t *args) {
	for (size_t i = 0; i < args->nitems; i++) {
		if (!eval(inter, args->items[i])) {
			return NULL;
		}
	}
	return newsym(inter, "true");
}

// (or a b c) returns the first non-null argument or null.
tok_t *or(t *inter, tok_t *args) {
	for (size_t i = 0; i < args->nitems; i++) {
		if (eval(inter, args->items[i])) {
			return newsym(inter, "true");
		}
	}
	return NULL;
}

tok_t *apply(t *inter, tok_t *list) {
	tok_t *fn = car(list);
	if (fn->type != SYMBOL) {
		dbgprint(list);
		panic("first element is a non-symbol");
	}
	return runfunc(inter, fn->name, eval(inter, car(cdr(inter, list))));
}

void printnum(char *buf, double x) {
	sprintf(buf, "%g", x);
}

double reduce(t *inter, tok_t *args, double start, int op) {
	if (args->type != LIST) {
		panic("not a list");
	}
	if (args->nitems < 2) {
		panic("want 2 or more arguments");
	}
	double r = start;
	for (size_t i = 0; i < args->nitems; i++) {
		tok_t *x = eval(inter, args->items[i]);
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
tok_t *mul(t *inter, tok_t *args) {
	char buf[100];
	printnum(buf, reduce(inter, args, 1, 1));
	return newnumber(inter, buf);
}

// (+ a b) returns a + b
tok_t *add(t *inter, tok_t *args) {
	char buf[100];
	printnum(buf, reduce(inter, args, 0, 2));
	return newnumber(inter, buf);
}

// (- a b) returns a - b
tok_t *sub(t *inter, tok_t *args) {
	char buf[100];

	tok_t *a = eval(inter, car(args));
	if (args->nitems == 1) {
		printnum(buf, -atof(a->value));
		return newnumber(inter, buf);
	}
	tok_t *b = eval(inter, car(cdr(inter, args)));
	if (a->type != NUMBER || b->type != NUMBER) {
		panic("not a number");
	}
	printnum(buf, atof(a->value) - atof(b->value));
	return newnumber(inter, buf);
}

// (/ a b) returns a / b
tok_t *over(t *inter, tok_t *args) {
	tok_t *a = eval(inter, car(args));
	tok_t *b = eval(inter, car(cdr(inter, args)));
	if (a->type != NUMBER || b->type != NUMBER) {
		dbgprint(args);
		panic("/: an argument is not a number");
	}
	char buf[100];
	printnum(buf, atof(a->value) / atof(b->value));
	return newnumber(inter, buf);
}

tok_t *numeq(t *inter, tok_t *args) {
	tok_t *a = eval(inter, car(args));
	tok_t *b = eval(inter, car(cdr(inter, args)));
	if (atof(a->value) == atof(b->value)) {
		return newsym(inter, "true");
	}
	return NULL;
}

// (eq? a b) returns true if a equals b.
tok_t *eq(t *inter, tok_t *args) {
	tok_t *a = eval(inter, car(args));
	tok_t *b = eval(inter, car(cdr(inter, args)));

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
tok_t *gt(t *inter, tok_t *args) {
	tok_t *a = eval(inter, car(args));
	tok_t *b = eval(inter, car(cdr(inter, args)));
	if (atof(a->value) > atof(b->value)) {
		return newsym(inter, "true");
	}
	return NULL;
}

// (< a b) returns true if a < b
tok_t *lt(t *inter, tok_t *args) {
	tok_t *a = eval(inter, car(args));
	tok_t *b = eval(inter, car(cdr(inter, args)));
	if (atof(a->value) < atof(b->value)) {
		return newsym(inter, "true");
	}
	return NULL;
}

// (cons 1 x) constructs a list (1, ...x)
tok_t *cons(t *inter, tok_t *args) {
	tok_t *head = car(args);
	tok_t *tail = car(cdr(inter, args));

	tok_t *r = newlist(inter);
	r->items[r->nitems++] = head;
	for (size_t i = 0; i < tail->nitems; i++) {
		r->items[r->nitems++] = tail->items[i];
	}
	return r;
}

// Returns the first item of the list x.
tok_t *car(tok_t *x) {
	if (x->type != LIST || x->nitems == 0) {
		return NULL;
	}
	return x->items[0];
}

// Returns the tail of the list x.
tok_t *cdr(t *inter, tok_t *x) {
	if (!x || x->type != LIST || x->nitems <= 1) {
		return NULL;
	}
	tok_t *r = newlist(inter);
	for (size_t i = 1; i < x->nitems; i++) {
		r->items[i-1] = x->items[i];
	}
	r->nitems = x->nitems-1;
	return r;
}

void printfn(binding_t *f) {
	printf("fn %s(", f->name);
	for (size_t i = 0; i < f->nargs; i++) {
		if (i > 0) printf(" ");
		printf("%s", f->argnames[i]);
	}
	printf(")");
}



void trace_indent(size_t depth) {
	for (size_t i = 0; i < depth; i++) printf("  ");
}

void trace_symbol_eval(t *inter, tok_t *x, *r) {
	if (!inter->trace) return;
	trace_indent(inter->depth);
	printf("EVAL_SYM %s: ", x->name);
	dbgprint(r);
}

void trace_list_before(t *inter, tok_t *x) {
	if (!inter->trace) return;
	trace_defs(inter);
	trace_indent(inter->depth);
	printf("eval: ");
	dbgprint(x);
}

void trace_defs(t *inter) {
	// -1 to exclude the first scope where built-in definitions are.
	for (size_t d = 0; d < inter->depth - 1; d++) {
		scope_t *s = inter->stack[inter->depth - d - 1];
		for (size_t i = 0; i < s->size; i++) {
			binding_t *d = &s->defs[i];
			printf("[%zu] %s = ", i, d->name);
			if (d->isfunc) {
				printfn(d);
				puts("");
			} else {
				dbgprint(d->val);
			}
		}
		puts("---");
	}
}

void trace_list_after(t *inter, tok_t *r) {
	if (!inter->trace) return;
	trace_indent(inter->depth);
	printf("result: ");
	dbgprint(r);
}

pub tok_t **readall(t *p, tokenizer.t *b) {
	tok_t **all = calloc(100, sizeof(b));
	size_t n = 0;
	while (true) {
		tok_t *t = readtok(p, b);
		if (!t) break;
		all[n++] = t;
	}
	return all;
}

// Reads next item from the buffer.
pub tok_t *readtok(t *p, tokenizer.t *b) {
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
tok_t *readnum(t *p, tokenizer.t *b) {
	char buf[100];
	if (!tokenizer.num(b, buf, 100)) {
		panic("failed to read a number");
	}
	return newnumber(p, buf);
}

// Reads a symbol.
tok_t *readsymbol(t *p, tokenizer.t *b) {
	tok_t *x = newsym(p, "");
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
tok_t *readlist(t *p, tokenizer.t *b) {
	tok_t *x = newlist(p);

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


enum {
	// UNKNOWN,
	LIST = 1,
	SYMBOL,
	NUMBER,
};

pub typedef {
	size_t mempos;

	int type;

	// for number:
	char *value;

	// for symbol:
	char *name;

	// for list:
	tok_t **items;
	size_t nitems;
} tok_t;



tok_t *alloc(t *inter) {
	for (size_t i = 0; i < inter->poolsize; i++) {
		size_t pos = (inter->last_alloc + i) % inter->poolsize;
		if (inter->in_use[pos]) {
			continue;
		}
		if (GCDEBUG) {
			printf("alloc at %zu\n", pos);
		}
		inter->in_use[pos] = true;
		inter->poolitems[pos].mempos = pos;
		inter->last_alloc = pos;
		return &inter->poolitems[pos];
	}
	if (GCDEBUG) {
		printf("OOM\n");
	}
	return NULL;
}

tok_t *make(t *p) {
	tok_t *x = alloc(p);
	if (!x) {
		gc(p);
		x = alloc(p);
		if (!x) {
			panic("out of memory");
		}
	}
	return x;
}

pub void gc(t *p) {
	if (GCDEBUG) {
		printf("depth = %zu, poolsize=%zu\n", p->depth, p->poolsize);
	}

	bitset.t *used = bitset.new(p->poolsize);

	for (size_t i = 0; i < p->depth; i++) {
		if (GCDEBUG) {
			printf("frame %zu\n-----------\n", i);
		}
		scope_t *s = p->stack[i];
		for (size_t j = 0; j < s->size; j++) {
			binding_t *b = &s->defs[j];
			if (GCDEBUG) {
				printf("%zu: %s\n", j, b->name);
			}
			gc_mark(used, p, b->val);
			if (b->isfunc) {
				for (size_t k = 0; k < b->nvals; k++) {
					gc_mark(used, p, b->vals[k]);
				}
			}
		}
	}

	size_t frees = 0;
	for (size_t i = 0; i < p->poolsize; i++) {
		if (!p->in_use[i] || bitset.isset(used, i)) {
			continue;
		}
		if (GCDEBUG) {
			printf("free %zu: ", i);
			dbgprint(&p->poolitems[i]);
		}
		p->in_use[i] = false;
		// memset(&p->poolitems[i], 0, sizeof(tok_t));
		frees++;
	}
	// printf("gc: %zu frees\n", frees);
	bitset.free(used);
}

void gc_mark(bitset.t *used, t *inter, tok_t *x) {
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
}

tok_t *newnumber(t *p, const char *val) {
	tok_t *x = make(p);
	x->type = NUMBER;
	x->value = calloc(60, 1);
	strcpy(x->value, val);
	return x;
}

tok_t *newlist(t *p) {
	tok_t *x = make(p);
	x->type = LIST;
	x->items = calloc(10, sizeof(x));
	return x;
}

tok_t *newsym(t *p, const char *s) {
	tok_t *x = make(p);
	x->type = SYMBOL;
	x->name = calloc(60, 1);
	strcpy(x->name, s);
	return x;
}



pub bool islist(tok_t *x, const char *name) {
	return x->type == LIST
		&& x->items[0]->type == SYMBOL
		&& !strcmp(x->items[0]->name, name);
}





// Prints the given item to stdout for debugging.
void dbgprint(tok_t *x) {
	char buf[4096];
	if (!x) {
		printf("NULL\n");
		return;
	}
	print(x, buf, 4096);
	printf("%s\n", buf);
}

// Prints the given node into the buf.
pub void print(tok_t *x, char *buf, size_t len) {
	strbuilder.str *s = strbuilder.str_new();
	_print(s, x);
	char *r = strbuilder.str_unpack(s);
	strncpy(buf, r, len);
	OS.free(r);
}

void _print(strbuilder.str *s, tok_t *x) {
	if (!x) {
		strbuilder.adds(s, "NULL");
		return;
	}
	// strbuilder.addf(s, "#%d ", x->mempos);
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
		default: {
			panic("unknown type");
		}
	}
}

#define TODOSIZE 100
#define TODOVOIDPSIZE 64

tok_t **compile(t *p, tok_t **in, size_t n) {
	tok_t **out = calloc(TODOSIZE, TODOVOIDPSIZE);
	int pos = 0;

	for (size_t i = 0; i < n; i++) {
		tok_t *x = in[i];

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

int compile_if(t *p, tok_t *x, tok_t *body[], int added) {
	// Tests the condition and skips the ok branch if false.
	tok_t *tst = newlist(p);
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

int compile_cond(t *p, tok_t *cond, tok_t *body[], int added) {
	for (size_t i = 1; i < cond->nitems; i++) {
		tok_t *alt = cond->items[i];

		// Tests the condtion and skips the ok expression if false.
		// Implies that cond values have exactly one expression.
		tok_t *tst = newlist(p);
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
