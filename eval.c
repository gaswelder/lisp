#import tok.c

// Represents a single binding.
pub typedef {
	bool isfunc;

	// Name of the function or constant.
	char name[80];

	// Argument names, if it's a function.
	size_t nargs;
	char argnames[10][10];

	// Constant value or function body.
	tok.tok_t *val;
} def_t;

// Scope is a list of bindings.
pub typedef {
	scope_t *parent;
	size_t size;
	def_t defs[100];
} scope_t;

// Finds a binding in the scope.
def_t *lookup(scope_t *s, const char *name) {
	for (size_t i = 0; i < s->size; i++) {
		if (!strcmp(name, s->defs[i].name)) {
			return &s->defs[i];
		}
	}
	return NULL;
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

// void printfn(fn_t *f) {
// 	printf("fn %s(", f->name);
// 	for (size_t i = 0; i < f->nargs; i++) {
// 		if (i > 0) printf(" ");
// 		printf("%s", f->argnames[i]);
// 	}
// 	printf(")");
// }

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

bool trace = false;
size_t depth = 0;

// Evaluates a node.
pub tok.tok_t *eval(scope_t *s, tok.tok_t *x) {
	if (x->type == tok.NUMBER) return x;
	if (x->type == tok.SYMBOL) {
		tok.tok_t *r = eval_symbol(s, x);
		if (trace) {
			for (size_t i = 0; i < depth; i++) printf("  ");
			printf("%s: ", x->name);
			tok.dbgprint(r);
		}
		return r;
	}
	depth++;
	if (depth == 100) {
		panic("eval stack overflow (%zu)", depth);
	}
	if (trace) {
		for (size_t i = 0; i < depth; i++) printf("  ");
		printf("eval: ");
		tok.dbgprint(x);
	}
	tok.tok_t *r = NULL;
	r = eval_list(s, x);
	if (trace) {
		for (size_t i = 0; i < depth; i++) printf("  ");
		printf("result: ");
		tok.dbgprint(r);
	}
	depth--;
	return r;
}

// Looks up a symbol.
tok.tok_t *eval_symbol(scope_t *s, tok.tok_t *x) {
	// if (!strcmp(x->name, "true") || !strcmp(x->name, "+") || !strcmp(x->name, "-")) {
	// 	return x;
	// }
	def_t *d = lookup(s, x->name);
	if (d) {
		return d->val;
	}
	return x;
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

	// See if there is a defined function with this name.
	def_t *f = lookup(s, name);
	if (!f) {
		panic("unknown function %s", name);
	}
	if (!f->isfunc) {
		panic("%s is not a function", name);
	}

	for (size_t a = 0; a < f->nargs; a++) {
		pushdef(s, f->argnames[a], eval(s, args->items[a]));
	}
	tok.tok_t *r = eval(s, f->val);
	s->size -= f->nargs;
	return r;	
}

// (define x const) defines a constant.
// (define (f x) body) defines a function.
tok.tok_t *define(scope_t *s, tok.tok_t *args) {
	tok.tok_t *def = car(args);
	tok.tok_t *val = car(cdr(args));
	if (def->type == tok.SYMBOL) {
		pushdef(s, def->name, eval(s, val));
		return NULL;
	}

	// (twice x) (* x 2)
	if (def->type == tok.LIST) {
		tok.tok_t *name = car(def);
		def_t *d = &s->defs[s->size++];
		strcpy(d->name, name->name);
		d->isfunc = true;
		d->val = val;
		for (size_t i = 1; i < def->nitems; i++) {
			strcpy(d->argnames[d->nargs++], def->items[i]->name);
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
		panic("not a number");
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
