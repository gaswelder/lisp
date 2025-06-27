#import tokenizer
#import vm.c

#define TODOSIZE 100
#define TODOVOIDPSIZE 64

pub typedef {
	void *vm;
} tt_t;

pub tt_t *new(size_t N) {
	tt_t *t = calloc(1, sizeof(tt_t));
	t->vm = newvm(N);
	return t;
}

// Frees an instance of the interpreter.
pub void free(tt_t *r) {
	// Ignore all the rest for now.
	OS.free(r);
}

// Parses a string into expressions, evaluates them,
// and prints results into the buffer out.
pub void evalstr(tt_t *t, const char *s, char *out, size_t n) {
	vm.val_t *r = vmevalstr(t->vm, s);
	vm.print(r, out, n);
}

pub int repl(tt_t *t, FILE *f) {
	vm.vm_t *in = t->vm;

	tokenizer.t *b = tokenizer.file(f);
	char buf[4096];
	while (true) {
		// Read a form.
		vm.val_t *x = readtok(in, b);
		if (!x) break;

		// Echo.
		printf("> ");
		vm.print(x, buf, 4096);
		puts(buf);

		// Evaluate and print.
		vm.val_t *r = eval(in, x);
		if (!islist(x, "define")) {
			vm.print(r, buf, 4096);
			puts(buf);
		}
	}

	// printf("%zu\n", in->poolsize);
	tokenizer.free(b);
	return 0;
}


vm.val_t *vmevalstr(vm.vm_t *inter, const char *s) {
	tokenizer.t *b = tokenizer.from_str(s);
	vm.val_t **all = readall(inter, b);
	tokenizer.free(b);

	vm.val_t *r = NULL;
	size_t n = 0;
	vm.val_t *x = all[n++];
	while (x) {
		r = eval(inter, x);
		x = all[n++];
	}
	return r;
}

// Creates a new instance of the interpreter.
vm.vm_t *newvm(size_t N) {
	vm.vm_t *r = vm.newvm(N);

	// Scope 0 for globals.
	r->stack[r->depth++] = vm.newscope();

	// These are special symbols used in compiled bodies for tail recursion.
	// They are stashed here in globals to keep them from being GC'd.
	vmevalstr(r, "(define __end __op_end)");
	vmevalstr(r, "(define __test_and_jump_if_false __op_test_and_jump_if_false)");

	// Scope 1 for predefined things.
	r->stack[r->depth++] = vm.newscope();

	// Define standard functions.
	vmevalstr(r, "
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
	r->stack[r->depth++] = vm.newscope();
	return r;
}

// Adds a binding to the scope.
void pushdef(vm.scope_t *s, const char *name, vm.val_t *val) {
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
vm.val_t *getdef(vm.scope_t *s, const char *n) {
	if (!n) {
		panic("n is null");
	}
	vm.val_t *r = NULL;
	for (size_t i = 0; i < s->size; i++) {
		if (!strcmp(n, s->names[i])) {
			// Don't break because redefinitions can be added further down.
			r = s->vals[i];
		}
	}
	return r;
}

vm.val_t *lookup(vm.vm_t *inter, const char *n) {
	if (!n) {
		panic("n is null");
	}
	for (size_t d = 0; d < inter->depth; d++) {
		vm.scope_t *s = inter->stack[inter->depth - 1 - d];
		vm.val_t *r = getdef(s, n);
		if (r) {
			return r;
		}
	}
	return NULL;
}

// Evaluates a node.
vm.val_t *eval(vm.vm_t *inter, vm.val_t *x) {
	if (!x) {
		panic("eval of NULL");
	}
	switch (x->type) {
		case vm.NUMBER: {
			return x;
		}
		case vm.SYMBOL: {
			// Look up the symbol.
			// If it's defined, use the definition.
			// If not, keep the symbol as is.
			vm.val_t *r = x;
			vm.val_t *d = lookup(inter, x->name);
			if (d) r = d;
			trace_symbol_eval(inter, x, r);
			return r;
		}
		case vm.LIST: {
			trace_list_before(inter, x);
			vm.val_t *r = eval_list(inter, x);
			trace_list_after(inter, r);
			return r;
		}
		case vm.FUNC: {
			return x;
		}
		default: {
			panic("unexpected value type");
		}
	}
}

// Evaluates a list node.
vm.val_t *eval_list(vm.vm_t *inter, vm.val_t *x) {
	// The first item could be anything, we might need to evaluate it
	// to find out which function to run.
	vm.val_t *first = vm.car(x);
	if (first->type == vm.LIST) {
		first = eval(inter, first);
	}
	// At this point we should have a symbol.
	if (first->type != vm.SYMBOL) {
		char buf[TODOSIZE];
		vm.print(first, buf, TODOSIZE);
		panic("invalid function invocation: got %s as function", buf);
	}
	return runfunc(inter, first->name, vm.cdr(inter, x));
}

// Runs a function.
vm.val_t *runfunc(vm.vm_t *inter, const char *name, vm.val_t *args) {
	if (inter->trace) {
		trace_indent(inter->depth);
		printf("RUN_FUNC: %s\n", name);
	}

	// See if there is a defined function with this name.
	// Custom definitions take precedence over the built-ins below.
	vm.val_t *f = lookup(inter, name);
	if (f) {
		return runcustomfunc(inter, f, args);
	}
	return run_builtin_func(inter, name, args);
}

vm.val_t *globalget(vm.vm_t *inter, const char *name) {
	return getdef(inter->stack[0], name);
}

vm.val_t *runcustomfunc(vm.vm_t *inter, vm.val_t *f, vm.val_t *args) {
	if (f->type != vm.FUNC) {
		panic("not a function");
	}

	// Check the arguments number.
	size_t nargs = 0;
	if (args) nargs = args->nitems;
	if (nargs != f->fn_nargs) {
		panic("function expects %u arguments, got %zu", f->fn_nargs, nargs);
	}

	// Create a new scope for the call.
	vm.scope_t *s2 = vm.newscope();
	for (size_t i = 0; i < f->fn_nargs; i++) {
		pushdef(s2, f->fn_argnames[i], eval(inter, args->items[i]));
	}
	inter->stack[inter->depth++] = s2;

	// The result of execution will be set here.
	vm.val_t *r = NULL;

	// Reformat the function body to have a better handle on execution
	// and execute each statement.
	vm.val_t **body = compile(inter, f->fn_statements, f->fn_nstatements);
	for (int i = 0; i < TODOSIZE; i++) {
		vm.val_t *x = body[i];

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
		// 	vm.scope_t *s3 = vm.newscope();
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

vm.val_t *run_builtin_func(vm.vm_t *inter, const char *name, vm.val_t *args) {
	switch str (name) {
		case "quote": { return fn_quote(args); }
		case "cons": { return fn_cons(inter, args); }
		case "apply": { return fn_apply(inter, args); }
		case "eq?": { return fn_eq(inter, args); }
		case "define": { return fn_define(inter, args); }
		case "*": { return fn_mul(inter, args); }
		case "+": { return fn_add(inter, args); }
		case "-": { return fn_sub(inter, args); }
		case "/": { return fn_over(inter, args); }
		case ">": { return fn_gt(inter, args); }
		case "<": { return fn_lt(inter, args); }
		case "=": { return fn_numeq(inter, args); }
		case "cond": { return fn_cond(inter, args); }
		case "if": { return fn_if(inter, args); }
		case "and": { return fn_and(inter, args); }
		case "or": { return fn_or(inter, args); }
		case "not": { return fn_not(inter, args); }
		case "__globalset": { return fn_globalset(inter, args); }
		case "__globalget": { return fn_globalget(inter, args); }
	}
	panic("unknown function: %s", name);
}

vm.val_t *fn_quote(vm.val_t *args) {
	return vm.car(args);
}

vm.val_t *fn_globalset(vm.vm_t *inter, vm.val_t *args) {
	vm.val_t *name = args->items[0];
	vm.val_t *val = eval(inter, args->items[1]);
	pushdef(inter->stack[0], name->name, val);
	return NULL;
}

vm.val_t *fn_globalget(vm.vm_t *inter, vm.val_t *args) {
	vm.val_t *name = args->items[0];
	return globalget(inter, name->name);
}

// (define x const) defines a constant.
// (define (f x) body) defines a function.
vm.val_t *fn_define(vm.vm_t *inter, vm.val_t *args) {
	vm.val_t *name = vm.first(args);
	vm.scope_t *s = inter->stack[inter->depth-1];

	// (define x const)
	if (name->type == vm.SYMBOL) {
		if (vm.len(args) != 2) {
			panic("constant define requires 2 args, got %zu", vm.len(args));
		}
		vm.val_t *val = vm.second(args);
		pushdef(s, name->name, eval(inter, val));
		return NULL;
	}

	// (define (twice x) (print x) (foo) (* x 2))
	if (name->type == vm.LIST) {
		const char *fnname = name->items[0]->name;
		vm.val_t *defargs = vm.slice(inter, name, 1);
		vm.val_t *defbody = vm.slice(inter, args, 1);
		pushdef(s, fnname, vm.newfunc(inter, defargs, defbody));
		return NULL;
	}

	vm.dbgprint(args);
	panic("unknown define shape");
}

vm.val_t *fn_cond(vm.vm_t *inter, vm.val_t *args) {
	vm.val_t *l = args;
	while (l) {
		vm.val_t *cas = vm.car(l);
		vm.val_t *cond = vm.car(cas);
		if (eval(inter, cond)) {
			vm.val_t *result = vm.car(vm.cdr(inter, cas));
			return eval(inter, result);
		}
		l = vm.cdr(inter, l);
	}
	return NULL;
}

// (not x) returns NULL if x is not null.
vm.val_t *fn_not(vm.vm_t *inter, vm.val_t *args) {
	if (eval(inter, vm.car(args))) {
		return NULL;
	}
	return vm.newsym(inter, "true");
}

// (if x then)
// (if x then else)
vm.val_t *fn_if(vm.vm_t *inter, vm.val_t *args) {
	vm.val_t *pred = vm.car(args);
	vm.val_t *ethen = vm.car(vm.cdr(inter, args));
	if (eval(inter, pred)) {
		return eval(inter, ethen);
	}
	if (args->nitems < 3) {
		return NULL;
	}
	vm.val_t *eelse = vm.car(vm.cdr(inter, vm.cdr(inter, args)));
	return eval(inter, eelse);
}

// (and a b c) returns c if a, b and c are not null.
// Returns null otherwise.
vm.val_t *fn_and(vm.vm_t *inter, vm.val_t *args) {
	for (size_t i = 0; i < args->nitems; i++) {
		if (!eval(inter, args->items[i])) {
			return NULL;
		}
	}
	return vm.newsym(inter, "true");
}

// (or a b c) returns the first non-null argument or null.
vm.val_t *fn_or(vm.vm_t *inter, vm.val_t *args) {
	for (size_t i = 0; i < args->nitems; i++) {
		if (eval(inter, args->items[i])) {
			return vm.newsym(inter, "true");
		}
	}
	return NULL;
}

vm.val_t *fn_apply(vm.vm_t *inter, vm.val_t *list) {
	vm.val_t *fn = vm.car(list);
	if (fn->type != vm.SYMBOL) {
		vm.dbgprint(list);
		panic("first element is a non-symbol");
	}
	return runfunc(inter, fn->name, eval(inter, vm.car(vm.cdr(inter, list))));
}

// (* a b) returns a * b
vm.val_t *fn_mul(vm.vm_t *inter, vm.val_t *args) {
	char buf[100];
	printnum(buf, reduce(inter, args, 1, 1));
	return vm.newnumber(inter, buf);
}

// (+ a b) returns a + b
vm.val_t *fn_add(vm.vm_t *inter, vm.val_t *args) {
	char buf[100];
	printnum(buf, reduce(inter, args, 0, 2));
	return vm.newnumber(inter, buf);
}

// (- a b) returns a - b
vm.val_t *fn_sub(vm.vm_t *inter, vm.val_t *args) {
	char buf[100];

	vm.val_t *a = eval(inter, vm.car(args));
	if (args->nitems == 1) {
		printnum(buf, -atof(a->value));
		return vm.newnumber(inter, buf);
	}
	vm.val_t *b = eval(inter, vm.car(vm.cdr(inter, args)));
	if (a->type != vm.NUMBER || b->type != vm.NUMBER) {
		panic("not a number");
	}
	printnum(buf, atof(a->value) - atof(b->value));
	return vm.newnumber(inter, buf);
}

// (/ a b) returns a / b
vm.val_t *fn_over(vm.vm_t *inter, vm.val_t *args) {
	vm.val_t *a = eval(inter, vm.car(args));
	vm.val_t *b = eval(inter, vm.car(vm.cdr(inter, args)));
	if (a->type != vm.NUMBER || b->type != vm.NUMBER) {
		vm.dbgprint(args);
		panic("/: an argument is not a number");
	}
	char buf[100];
	printnum(buf, atof(a->value) / atof(b->value));
	return vm.newnumber(inter, buf);
}

vm.val_t *fn_numeq(vm.vm_t *inter, vm.val_t *args) {
	vm.val_t *a = eval(inter, vm.car(args));
	vm.val_t *b = eval(inter, vm.car(vm.cdr(inter, args)));
	if (atof(a->value) == atof(b->value)) {
		return vm.newsym(inter, "true");
	}
	return NULL;
}

// (eq? a b) returns true if a equals b.
vm.val_t *fn_eq(vm.vm_t *inter, vm.val_t *args) {
	vm.val_t *a = eval(inter, vm.car(args));
	vm.val_t *b = eval(inter, vm.car(vm.cdr(inter, args)));

	// If types don't match, then not equal.
	if (a->type != b->type) {
		return NULL;
	}
	bool same = false;
	switch (a->type) {
		case vm.SYMBOL: { same = !strcmp(a->name, b->name); }
		case vm.NUMBER: { same = !strcmp(a->value, b->value); }
		default: {
			panic("unhandled item type: %d", a->type);
		}
	}
	if (same) {
		return vm.newsym(inter, "true");
	}
	return NULL;
}

// (> a b) returns true if a > b
vm.val_t *fn_gt(vm.vm_t *inter, vm.val_t *args) {
	vm.val_t *a = eval(inter, vm.car(args));
	vm.val_t *b = eval(inter, vm.car(vm.cdr(inter, args)));
	if (atof(a->value) > atof(b->value)) {
		return vm.newsym(inter, "true");
	}
	return NULL;
}

// (< a b) returns true if a < b
vm.val_t *fn_lt(vm.vm_t *inter, vm.val_t *args) {
	vm.val_t *a = eval(inter, vm.car(args));
	vm.val_t *b = eval(inter, vm.car(vm.cdr(inter, args)));
	if (atof(a->value) < atof(b->value)) {
		return vm.newsym(inter, "true");
	}
	return NULL;
}

// (cons 1 x) constructs a list (1, ...x)
vm.val_t *fn_cons(vm.vm_t *inter, vm.val_t *args) {
	vm.val_t *head = vm.car(args);
	vm.val_t *tail = vm.car(vm.cdr(inter, args));

	vm.val_t *r = vm.newlist(inter);
	r->items[r->nitems++] = head;
	for (size_t i = 0; i < tail->nitems; i++) {
		r->items[r->nitems++] = tail->items[i];
	}
	return r;
}

void printnum(char *buf, double x) {
	sprintf(buf, "%g", x);
}

double reduce(vm.vm_t *inter, vm.val_t *args, double start, int op) {
	if (args->type != vm.LIST) {
		panic("not a list");
	}
	if (args->nitems < 2) {
		panic("want 2 or more arguments");
	}
	double r = start;
	for (size_t i = 0; i < args->nitems; i++) {
		vm.val_t *x = eval(inter, args->items[i]);
		if (x->type != vm.NUMBER) {
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

void trace_indent(size_t depth) {
	for (size_t i = 0; i < depth; i++) printf("  ");
}

void trace_symbol_eval(vm.vm_t *inter, vm.val_t *x, *r) {
	if (!inter->trace) return;
	trace_indent(inter->depth);
	printf("EVAL_SYM %s: ", x->name);
	vm.dbgprint(r);
}

void trace_list_before(vm.vm_t *inter, vm.val_t *x) {
	if (!inter->trace) return;
	trace_defs(inter);
	trace_indent(inter->depth);
	printf("eval: ");
	vm.dbgprint(x);
}

void print_scope(vm.scope_t *s) {
	for (size_t i = 0; i < s->size; i++) {
		printf("[%zu] %s = ", i, s->names[i]);
		vm.dbgprint(s->vals[i]);
	}
	puts("---");
}

void trace_defs(vm.vm_t *inter) {
	// -1 to exclude the first scope where built-in definitions are.
	for (size_t d = 0; d < inter->depth - 1; d++) {
		vm.scope_t *s = inter->stack[inter->depth - d - 1];
		print_scope(s);
	}
}

void trace_list_after(vm.vm_t *inter, vm.val_t *r) {
	if (!inter->trace) return;
	trace_indent(inter->depth);
	printf("result: ");
	vm.dbgprint(r);
}

vm.val_t **readall(vm.vm_t *p, tokenizer.t *b) {
	vm.val_t **all = calloc(100, sizeof(b));
	size_t n = 0;
	while (true) {
		vm.val_t *t = readtok(p, b);
		if (!t) break;
		all[n++] = t;
	}
	return all;
}

// Reads next item from the buffer.
vm.val_t *readtok(vm.vm_t *p, tokenizer.t *b) {
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
vm.val_t *readnum(vm.vm_t *p, tokenizer.t *b) {
	char buf[100];
	if (!tokenizer.num(b, buf, 100)) {
		panic("failed to read a number");
	}
	return vm.newnumber(p, buf);
}

// Reads a symbol.
vm.val_t *readsymbol(vm.vm_t *p, tokenizer.t *b) {
	vm.val_t *x = vm.newsym(p, "");
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
vm.val_t *readlist(vm.vm_t *p, tokenizer.t *b) {
	vm.val_t *x = vm.newlist(p);

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

bool islist(vm.val_t *x, const char *name) {
	return x->type == vm.LIST
		&& x->items[0]->type == vm.SYMBOL
		&& !strcmp(x->items[0]->name, name);
}

bool is_symbol(vm.val_t *x, const char *name) {
	return x->type == vm.SYMBOL && !strcmp(x->name, name);
}

vm.val_t **compile(vm.vm_t *p, vm.val_t **in, size_t n) {
	vm.val_t **out = calloc(TODOSIZE, TODOVOIDPSIZE);
	int pos = 0;

	for (size_t i = 0; i < n; i++) {
		vm.val_t *x = in[i];

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

int compile_if(vm.vm_t *p, vm.val_t *x, vm.val_t *body[], int added) {
	// Tests the condition and skips the ok branch if false.
	vm.val_t *tst = vm.newlist(p);
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

int compile_cond(vm.vm_t *p, vm.val_t *cond, vm.val_t *body[], int added) {
	for (size_t i = 1; i < cond->nitems; i++) {
		vm.val_t *alt = cond->items[i];

		// Tests the condtion and skips the ok expression if false.
		// Implies that cond values have exactly one expression.
		vm.val_t *tst = vm.newlist(p);
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
