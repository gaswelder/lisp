#import tok.c
#import os/self

// Represents a single binding.
pub typedef {
	bool isfunc;

	// Name of the function or constant.
	char name[80];

	// constant:
	tok.tok_t *val;

	// function:
	size_t nargs;
	char argnames[10][10];
	size_t nvals;
	tok.tok_t *vals[100];
} def_t;

// Scope is a list of bindings.
pub typedef {
	scope_t *parent;
	size_t size;
	def_t defs[100];
} scope_t;

// Finds a binding in the scope.
def_t *lookup(scope_t *s, const char *name) {
	def_t *r = NULL;
	for (size_t i = 0; i < s->size; i++) {
		if (!strcmp(name, s->defs[i].name)) {
			r = &s->defs[i];
		}
	}
	if (!r && s->parent) {
		return lookup(s->parent, name);
	}
	return r;
}

pub scope_t *newscope() {
	scope_t *s = calloc(1, sizeof(scope_t));
	if (!s) panic("calloc failed");
	return s;
}

// Adds a binding to the scope.
void pushdef(scope_t *s, const char *name, tok.tok_t *val) {
	strcpy(s->defs[s->size].name, name);
	s->defs[s->size].val = val;
	s->size++;
}

pub tok.tok_t *evalall(scope_t *s, tok.tok_t **all) {
	tok.tok_t *r = NULL;
	size_t n = 0;
	tok.tok_t *x = all[n++];
	while (x) {
		r = eval(s, x);
		x = all[n++];
	}
	return r;
}

size_t depth = 0;

// Evaluates a node.
pub tok.tok_t *eval(scope_t *s, tok.tok_t *x) {
	trace_init();

	if (x->type == tok.NUMBER) {
		return x;
	}
	if (x->type == tok.SYMBOL) {
		// Look up the symbol.
		// If it's defined, use the definition.
		// If not, keep the symbol as is.
		tok.tok_t *r = x;
		def_t *d = lookup(s, x->name);
		if (d) r = d->val;
		trace_symbol_eval(x, r);
		return r;
	}
	if (x->type == tok.LIST) {
		depth++;
		if (depth == 100) {
			panic("eval stack overflow (%zu)", depth);
		}
		trace_list_before(s, x);
		tok.tok_t *r = NULL;
		r = eval_list(s, x);
		trace_list_after(r);
		depth--;
		return r;
	}
	panic("unexpected value type");
}

// Evaluates a list node.
tok.tok_t *eval_list(scope_t *s, tok.tok_t *x) {
	tok.tok_t *first = car(x);
	if (first->type != tok.SYMBOL) {
		first = eval(s, first);
	}
	return runfunc(s, first->name, cdr(x));
}

// Runs a function.
tok.tok_t *runfunc(scope_t *s, const char *name, tok.tok_t *args) {
	// See if there is a defined function with this name.
	// Custom definitions take precence over the built-ins below.
	def_t *f = lookup(s, name);
	if (f) {
		if (!f->isfunc) {
			panic("%s is not a function", name);
		}
		scope_t *s2 = newscope();
		s2->parent = s;
		for (size_t a = 0; a < f->nargs; a++) {
			pushdef(s2, f->argnames[a], eval(s, args->items[a]));
		}
		tok.tok_t *r = NULL;
		for (size_t i = 0; i < f->nvals; i++) {
			r = eval(s2, f->vals[i]);
		}
		return r;
	}

	switch str (name) {
		case "quote": { return car(args); }
		case "cons": { return cons(args); }

		case "apply": { return apply(s, args); }
		case "eq?": { return eq(s, args); }
		case "define": { return define(s, args); }
		case "*": { return mul(s, args); }
		case "+": { return add(s, args); }
		case "-": { return sub(s, args); }
		case "/": { return over(s, args); }
		case ">": { return gt(s, args); }
		case "<": { return lt(s, args); }
		case "=": { return numeq(s, args); }
		case "cond": { return cond(s, args); }
		case "if": { return fif(s, args); }
		case "and": { return and(s, args); }
		case "or": { return or(s, args); }
		case "not": { return not(s, args); }
	}
	panic("unknown function: %s", name);
}

// (define x const) defines a constant.
// (define (f x) body) defines a function.
tok.tok_t *define(scope_t *s, tok.tok_t *args) {
	tok.tok_t *def = car(args);

	if (def->type == tok.SYMBOL) {
		tok.tok_t *val = car(cdr(args));
		pushdef(s, def->name, eval(s, val));
		return NULL;
	}

	// (twice x) (print x) (foo) (* x 2)
	if (def->type == tok.LIST) {
		def_t *d = &s->defs[s->size++];
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

	tok.dbgprint(args);
	panic("unknown define shape");
}


tok.tok_t *cond(scope_t *s, tok.tok_t *args) {
	tok.tok_t *l = args;
	while (l) {
		tok.tok_t *cas = car(l);
		tok.tok_t *cond = car(cas);
		if (eval(s, cond)) {
			tok.tok_t *result = car(cdr(cas));
			return eval(s, result);
		}
		l = cdr(l);
	}
	return NULL;
}

// (not x) returns NULL if x is not null.
tok.tok_t *not(scope_t *s, tok.tok_t *args) {
	if (eval(s, car(args))) {
		return NULL;
	}
	return tok.newsym("true");
}

// (if x then)
// (if x then else)
tok.tok_t *fif(scope_t *s, tok.tok_t *args) {
	tok.tok_t *pred = car(args);
	tok.tok_t *ethen = car(cdr(args));
	if (eval(s, pred)) {
		return eval(s, ethen);
	}
	if (args->nitems < 3) {
		return NULL;
	}
	tok.tok_t *eelse = car(cdr(cdr(args)));
	return eval(s, eelse);
}

// (and a b c) returns c if a, b and c are not null.
// Returns null otherwise.
tok.tok_t *and(scope_t *s, tok.tok_t *args) {
	for (size_t i = 0; i < args->nitems; i++) {
		if (!eval(s, args->items[i])) {
			return NULL;
		}
	}
	return tok.newsym("true");
}

// (or a b c) returns the first non-null argument or null.
tok.tok_t *or(scope_t *s, tok.tok_t *args) {
	for (size_t i = 0; i < args->nitems; i++) {
		if (eval(s, args->items[i])) {
			return tok.newsym("true");
		}
	}
	return NULL;
}

tok.tok_t *apply(scope_t *s, tok.tok_t *list) {
	tok.tok_t *fn = car(list);
	if (fn->type != tok.SYMBOL) {
		tok.dbgprint(list);
		panic("first element is a non-symbol");
	}
	return runfunc(s, fn->name, eval(s, car(cdr(list))));
}

void printnum(char *buf, double x) {
	sprintf(buf, "%g", x);
}

double reduce(scope_t *s, tok.tok_t *args, double start, int op) {
	if (args->type != tok.LIST) {
		panic("not a list");
	}
	if (args->nitems < 2) {
		panic("want 2 or more arguments");
	}
	double r = start;
	for (size_t i = 0; i < args->nitems; i++) {
		tok.tok_t *x = eval(s, args->items[i]);
		if (x->type != tok.NUMBER) {
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
tok.tok_t *mul(scope_t *s, tok.tok_t *args) {
	char buf[100];
	printnum(buf, reduce(s, args, 1, 1));
	return tok.newnumber(buf);
}

// (+ a b) returns a + b
tok.tok_t *add(scope_t *s, tok.tok_t *args) {
	char buf[100];
	printnum(buf, reduce(s, args, 0, 2));
	return tok.newnumber(buf);
}

// (- a b) returns a - b
tok.tok_t *sub(scope_t *s, tok.tok_t *args) {
	char buf[100];

	tok.tok_t *a = eval(s, car(args));
	if (args->nitems == 1) {
		printnum(buf, -atof(a->value));
		return tok.newnumber(buf);
	}
	tok.tok_t *b = eval(s, car(cdr(args)));
	if (a->type != tok.NUMBER || b->type != tok.NUMBER) {
		panic("not a number");
	}
	printnum(buf, atof(a->value) - atof(b->value));
	return tok.newnumber(buf);
}

// (/ a b) returns a / b
tok.tok_t *over(scope_t *s, tok.tok_t *args) {
	tok.tok_t *a = eval(s, car(args));
	tok.tok_t *b = eval(s, car(cdr(args)));
	if (a->type != tok.NUMBER || b->type != tok.NUMBER) {
		tok.dbgprint(args);
		panic("/: an argument is not a number");
	}
	char buf[100];
	printnum(buf, atof(a->value) / atof(b->value));
	return tok.newnumber(buf);
}

tok.tok_t *numeq(scope_t *s, tok.tok_t *args) {
	tok.tok_t *a = eval(s, car(args));
	tok.tok_t *b = eval(s, car(cdr(args)));
	if (atof(a->value) == atof(b->value)) {
		return tok.newsym("true");
	}
	return NULL;
}

// (eq? a b) returns true if a equals b.
tok.tok_t *eq(scope_t *s, tok.tok_t *args) {
	tok.tok_t *a = eval(s, car(args));
	tok.tok_t *b = eval(s, car(cdr(args)));

	// If types don't match, then not equal.
	if (a->type != b->type) {
		return NULL;
	}
	bool same = false;
	switch (a->type) {
		case tok.SYMBOL: { same = !strcmp(a->name, b->name); }
		case tok.NUMBER: { same = !strcmp(a->value, b->value); }
		default: {
			panic("unhandled item type: %d", a->type);
		}
	}
	if (same) {
		return tok.newsym("true");
	}
	return NULL;
}

// (> a b) returns true if a > b
tok.tok_t *gt(scope_t *s, tok.tok_t *args) {
	tok.tok_t *a = eval(s, car(args));
	tok.tok_t *b = eval(s, car(cdr(args)));
	if (atof(a->value) > atof(b->value)) {
		return tok.newsym("true");
	}
	return NULL;
}

// (< a b) returns true if a < b
tok.tok_t *lt(scope_t *s, tok.tok_t *args) {
	tok.tok_t *a = eval(s, car(args));
	tok.tok_t *b = eval(s, car(cdr(args)));
	if (atof(a->value) < atof(b->value)) {
		return tok.newsym("true");
	}
	return NULL;
}

// (cons 1 x) constructs a list (1, ...x)
tok.tok_t *cons(tok.tok_t *args) {
	tok.tok_t *head = car(args);
	tok.tok_t *tail = car(cdr(args));

	tok.tok_t *r = tok.newlist();
	r->items[r->nitems++] = head;
	for (size_t i = 0; i < tail->nitems; i++) {
		r->items[r->nitems++] = tail->items[i];
	}
	return r;
}

// Returns the first item of the list x.
tok.tok_t *car(tok.tok_t *x) {
	if (x->type != tok.LIST || x->nitems == 0) {
		return NULL;
	}
	return x->items[0];
}

// Returns the tail of the list x.
tok.tok_t *cdr(tok.tok_t *x) {
	if (!x || x->type != tok.LIST || x->nitems <= 1) {
		return NULL;
	}
	tok.tok_t *r = tok.newlist();
	for (size_t i = 1; i < x->nitems; i++) {
		r->items[i-1] = x->items[i];
	}
	r->nitems = x->nitems-1;
	return r;
}

bool trace = false;
bool _traceset = false;

void printfn(def_t *f) {
	printf("fn %s(", f->name);
	for (size_t i = 0; i < f->nargs; i++) {
		if (i > 0) printf(" ");
		printf("%s", f->argnames[i]);
	}
	printf(")");
}

void trace_defs(scope_t *s) {
	for (size_t i = 0; i < s->size; i++) {
		def_t *d = &s->defs[i];
		printf("- [%zu] %s = ", i, d->name);
		if (d->isfunc) {
			printfn(d);
			puts("");
		} else {
			tok.dbgprint(d->val);
		}
	}
	if (s->parent) {
		puts("---");
		trace_defs(s->parent);
	}
}

void trace_init() {
	if (!_traceset) {
		_traceset = true;
		const char *v = self.getenv("DEBUG");
		if (v && strcmp(v, "0")) {
			trace = true;
		}
	}
}

void trace_indent() {
	for (size_t i = 0; i < depth; i++) printf("  ");
}

void trace_symbol_eval(tok.tok_t *x, *r) {
	if (!trace) return;
	trace_indent();
	printf("%s: ", x->name);
	tok.dbgprint(r);
}

void trace_list_before(scope_t *s, tok.tok_t *x) {
	if (!trace) return;
	trace_defs(s);
	trace_indent();
	printf("eval: ");
	tok.dbgprint(x);
}

void trace_list_after(tok.tok_t *r) {
	if (!trace) return;
	trace_indent();
	printf("result: ");
	tok.dbgprint(r);
}
