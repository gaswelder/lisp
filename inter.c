#import os/self
#import read.c
#import tok.c
#import tokenizer

// An instance of the interpreter, with all its internal state.
pub typedef {
    scope_t *stack[400];
    size_t depth;
} t;

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

// Scope is a list of bindings, a call stack frame.
pub typedef {
	size_t size;
	def_t defs[100];
} scope_t;

// Creates a new instance of the interpreter.
pub t *new() {
    t *r = calloc(1, sizeof(t));
    if (!r) panic("calloc failed");
    r->stack[r->depth++] = newscope();

    // Define standard functions.
    evalstr(r, "(define (abs x) (if (> x 0) x (- x)))");
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
void pushdef(scope_t *s, const char *name, tok.tok_t *val) {
	strcpy(s->defs[s->size].name, name);
	s->defs[s->size].val = val;
	s->size++;
}

// Finds a binding.
def_t *lookup(t *inter, const char *name) {
    for (size_t d = 0; d < inter->depth; d++) {
        scope_t *s = inter->stack[inter->depth - 1 - d];
        def_t *r = NULL;
        for (size_t i = 0; i < s->size; i++) {
            if (!strcmp(name, s->defs[i].name)) {
                r = &s->defs[i];
            }
        }
        if (r) {
            return r;
        }
    }
	return NULL;
}

// Parses a string into expressions and evaluates them.
pub tok.tok_t *evalstr(t *inter, const char *s) {
    tokenizer.t *b = tokenizer.from_str(s);
	tok.tok_t **all = read.readall(b);
	tokenizer.free(b);

	tok.tok_t *r = NULL;
	size_t n = 0;
	tok.tok_t *x = all[n++];
	while (x) {
		r = eval(inter, x);
		x = all[n++];
	}
	return r;
}

// Evaluates a node.
pub tok.tok_t *eval(t *inter, tok.tok_t *x) {
    trace_init();

	if (x->type == tok.NUMBER) {
		return x;
	}
	if (x->type == tok.SYMBOL) {
		// Look up the symbol.
		// If it's defined, use the definition.
		// If not, keep the symbol as is.
		tok.tok_t *r = x;
		def_t *d = lookup(inter, x->name);
		if (d) r = d->val;
		trace_symbol_eval(inter->depth, x, r);
		return r;
	}
	if (x->type == tok.LIST) {
		trace_list_before(inter, x);
		tok.tok_t *r = eval_list(inter, x);
		trace_list_after(inter, r);
		return r;
	}
	panic("unexpected value type");
}

// Evaluates a list node.
tok.tok_t *eval_list(t *inter, tok.tok_t *x) {
	// The first item could be anything, we might need to evaluate it
	// to find out which function to run.
	tok.tok_t *first = car(x);
	if (first->type == tok.LIST) {
		first = eval(inter, first);
	}
	// At this point we should have a symbol.
	if (first->type != tok.SYMBOL) {
		char buf[100];
		tok.print(first, buf, 100);
		panic("invalid function invocation: got %s as function", buf);
	}
	return runfunc(inter, first->name, cdr(x));
}

// Runs a function.
tok.tok_t *runfunc(t *inter, const char *name, tok.tok_t *args) {
	// See if there is a defined function with this name.
	// Custom definitions take precedence over the built-ins below.
	def_t *f = lookup(inter, name);
	if (f) {
		return runcustomfunc(inter, f, args);
	}

	switch str (name) {
		case "quote": { return car(args); }
		case "cons": { return cons(args); }

		case "apply": { return apply(inter, args); }
		case "eq?": { return eq(inter, args); }
		case "define": { return define(inter, args); }
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
	}
	panic("unknown function: %s", name);
}

int compile_if(tok.tok_t *x, tok.tok_t *body[]) {
	int added = 0;

	// Tests the condition and skips the ok branch if false.
	tok.tok_t *tst = tok.newlist();
	tst->items[tst->nitems++] = tok.newsym("__test_and_jump_if_false");
	tst->items[tst->nitems++] = x->items[1];
	body[added++] = tst;

	// The ok branch with an end marker.
	body[added++] = x->items[2];
	body[added++] = tok.newsym("__end");

	// The else branch.
	body[added++] = x->items[3];

	return added;
}

int compile_cond(tok.tok_t *cond, tok.tok_t *body[]) {
	int added = 0;

	for (size_t i = 1; i < cond->nitems; i++) {
		tok.tok_t *alt = cond->items[i];

		// Tests the condtion and skips the ok expression if false.
		// Implies that cond values have exactly one expression.
		tok.tok_t *tst = tok.newlist();
		tst->items[tst->nitems++] = tok.newsym("__test_and_jump_if_false");
		tst->items[tst->nitems++] = alt->items[0];
		body[added++] = tst;

		// Value followed by the stop command
		// (implies that this cond is the last expression)
		body[added++] = alt->items[1];
		body[added++] = tok.newsym("__end");
	}
	return added;
}

bool islist(tok.tok_t *x, const char *name) {
	return x->type == tok.LIST
		&& x->items[0]->type == tok.SYMBOL
		&& !strcmp(x->items[0]->name, name);
}

tok.tok_t *runcustomfunc(t *inter, def_t *f, tok.tok_t *args) {
	if (!f->isfunc) {
		panic("%s is not a function", f->name);
	}

	// Reformat the function body to have a better handle on execution.
	tok.tok_t *body[100] = {};
	int added = 0;
	for (size_t i = 0; i < f->nvals; i++) {
		tok.tok_t *x = f->vals[i];
		// Flatten ifs at the end so we can attempt a tail recursion.
		if (i == f->nvals - 1 && islist(x, "if")) {
			added += compile_if(x, body);
			continue;
		}
		if (i == f->nvals - 1 && islist(x, "cond")) {
			added += compile_cond(x, body);
			continue;
		}
		body[added++] = x;
	}

	// Create a new scope for the call.
	scope_t *s2 = newscope();
	for (size_t a = 0; a < f->nargs; a++) {
		pushdef(s2, f->argnames[a], eval(inter, args->items[a]));
	}
    inter->stack[inter->depth++] = s2;

	tok.tok_t *r = NULL;
	for (int i = 0; i < 100; i++) {
		tok.tok_t *x = body[i];
		if (!x) break;
		if (x->type == tok.SYMBOL && !strcmp(x->name, "__end")) {
			break;
		}
		if (islist(x, "__test_and_jump_if_false")) {
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
			continue;
		}

		r = eval(inter, x);
	}

    inter->depth--;
	return r;
}

// (define x const) defines a constant.
// (define (f x) body) defines a function.
tok.tok_t *define(t *inter, tok.tok_t *args) {
	tok.tok_t *def = car(args);

    // (define x const)
	if (def->type == tok.SYMBOL) {
		tok.tok_t *val = car(cdr(args));
        scope_t *s = inter->stack[inter->depth-1];
		pushdef(s, def->name, eval(inter, val));
		return NULL;
	}

	// (define (twice x) (print x) (foo) (* x 2))
	if (def->type == tok.LIST) {
        scope_t *s = inter->stack[inter->depth-1];
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


tok.tok_t *cond(t *inter, tok.tok_t *args) {
	tok.tok_t *l = args;
	while (l) {
		tok.tok_t *cas = car(l);
		tok.tok_t *cond = car(cas);
		if (eval(inter, cond)) {
			tok.tok_t *result = car(cdr(cas));
			return eval(inter, result);
		}
		l = cdr(l);
	}
	return NULL;
}

// (not x) returns NULL if x is not null.
tok.tok_t *not(t *inter, tok.tok_t *args) {
	if (eval(inter, car(args))) {
		return NULL;
	}
	return tok.newsym("true");
}

// (if x then)
// (if x then else)
tok.tok_t *fif(t *inter, tok.tok_t *args) {
	tok.tok_t *pred = car(args);
	tok.tok_t *ethen = car(cdr(args));
	if (eval(inter, pred)) {
		return eval(inter, ethen);
	}
	if (args->nitems < 3) {
		return NULL;
	}
	tok.tok_t *eelse = car(cdr(cdr(args)));
	return eval(inter, eelse);
}

// (and a b c) returns c if a, b and c are not null.
// Returns null otherwise.
tok.tok_t *and(t *inter, tok.tok_t *args) {
	for (size_t i = 0; i < args->nitems; i++) {
		if (!eval(inter, args->items[i])) {
			return NULL;
		}
	}
	return tok.newsym("true");
}

// (or a b c) returns the first non-null argument or null.
tok.tok_t *or(t *inter, tok.tok_t *args) {
	for (size_t i = 0; i < args->nitems; i++) {
		if (eval(inter, args->items[i])) {
			return tok.newsym("true");
		}
	}
	return NULL;
}

tok.tok_t *apply(t *inter, tok.tok_t *list) {
	tok.tok_t *fn = car(list);
	if (fn->type != tok.SYMBOL) {
		tok.dbgprint(list);
		panic("first element is a non-symbol");
	}
	return runfunc(inter, fn->name, eval(inter, car(cdr(list))));
}

void printnum(char *buf, double x) {
	sprintf(buf, "%g", x);
}

double reduce(t *inter, tok.tok_t *args, double start, int op) {
	if (args->type != tok.LIST) {
		panic("not a list");
	}
	if (args->nitems < 2) {
		panic("want 2 or more arguments");
	}
	double r = start;
	for (size_t i = 0; i < args->nitems; i++) {
		tok.tok_t *x = eval(inter, args->items[i]);
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
tok.tok_t *mul(t *inter, tok.tok_t *args) {
	char buf[100];
	printnum(buf, reduce(inter, args, 1, 1));
	return tok.newnumber(buf);
}

// (+ a b) returns a + b
tok.tok_t *add(t *inter, tok.tok_t *args) {
	char buf[100];
	printnum(buf, reduce(inter, args, 0, 2));
	return tok.newnumber(buf);
}

// (- a b) returns a - b
tok.tok_t *sub(t *inter, tok.tok_t *args) {
	char buf[100];

	tok.tok_t *a = eval(inter, car(args));
	if (args->nitems == 1) {
		printnum(buf, -atof(a->value));
		return tok.newnumber(buf);
	}
	tok.tok_t *b = eval(inter, car(cdr(args)));
	if (a->type != tok.NUMBER || b->type != tok.NUMBER) {
		panic("not a number");
	}
	printnum(buf, atof(a->value) - atof(b->value));
	return tok.newnumber(buf);
}

// (/ a b) returns a / b
tok.tok_t *over(t *inter, tok.tok_t *args) {
	tok.tok_t *a = eval(inter, car(args));
	tok.tok_t *b = eval(inter, car(cdr(args)));
	if (a->type != tok.NUMBER || b->type != tok.NUMBER) {
		tok.dbgprint(args);
		panic("/: an argument is not a number");
	}
	char buf[100];
	printnum(buf, atof(a->value) / atof(b->value));
	return tok.newnumber(buf);
}

tok.tok_t *numeq(t *inter, tok.tok_t *args) {
	tok.tok_t *a = eval(inter, car(args));
	tok.tok_t *b = eval(inter, car(cdr(args)));
	if (atof(a->value) == atof(b->value)) {
		return tok.newsym("true");
	}
	return NULL;
}

// (eq? a b) returns true if a equals b.
tok.tok_t *eq(t *inter, tok.tok_t *args) {
	tok.tok_t *a = eval(inter, car(args));
	tok.tok_t *b = eval(inter, car(cdr(args)));

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
tok.tok_t *gt(t *inter, tok.tok_t *args) {
	tok.tok_t *a = eval(inter, car(args));
	tok.tok_t *b = eval(inter, car(cdr(args)));
	if (atof(a->value) > atof(b->value)) {
		return tok.newsym("true");
	}
	return NULL;
}

// (< a b) returns true if a < b
tok.tok_t *lt(t *inter, tok.tok_t *args) {
	tok.tok_t *a = eval(inter, car(args));
	tok.tok_t *b = eval(inter, car(cdr(args)));
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



void trace_init() {
	if (!_traceset) {
		_traceset = true;
		const char *v = self.getenv("DEBUG");
		if (v && strcmp(v, "0")) {
			trace = true;
		}
	}
}

void trace_indent(size_t depth) {
	for (size_t i = 0; i < depth; i++) printf("  ");
}

void trace_symbol_eval(size_t depth, tok.tok_t *x, *r) {
	if (!trace) return;
	trace_indent(depth);
	printf("%s: ", x->name);
	tok.dbgprint(r);
}

void trace_list_before(t *inter, tok.tok_t *x) {
	if (!trace) return;
	trace_defs(inter);
	trace_indent(inter->depth);
	printf("eval: ");
	tok.dbgprint(x);
}

void trace_defs(t *inter) {
    for (size_t d = 0; d < inter->depth; d++) {
        scope_t *s = inter->stack[inter->depth - d - 1];
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
        puts("---");
    }
}

void trace_list_after(t *inter, tok.tok_t *r) {
	if (!trace) return;
	trace_indent(inter->depth);
	printf("result: ");
	tok.dbgprint(r);
}
