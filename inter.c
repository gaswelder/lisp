#import tokenizer
#import vm.c
#import vmread.c
#import vmcomp.c

#define TODOSIZE 100

const char *STDLIB = "
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
";

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
		vm.val_t *x = vmread.readtok(in, b);
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
	vm.val_t **all = vmread.readall(inter, s);
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
	vmevalstr(r, STDLIB);

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
			vm.val_t *d = vm.lookup(inter, x->sym.name);
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
	return eval_func(inter, first->sym.name, vm.cdr(inter, x));
}

// Evaluates a function node.
vm.val_t *eval_func(vm.vm_t *inter, const char *name, vm.val_t *args) {
	if (inter->trace) {
		trace_indent(inter->depth);
		printf("RUN_FUNC: %s\n", name);
	}

	// See if there is a defined function with this name.
	// Custom definitions take precedence over the built-ins below.
	vm.val_t *f = vm.lookup(inter, name);
	if (f) {
		return runcustomfunc(inter, f, args);
	}
	return run_builtin_func(inter, name, args);
}

vm.val_t *runcustomfunc(vm.vm_t *inter, vm.val_t *f, vm.val_t *args) {
	if (f->type != vm.FUNC) {
		panic("not a function");
	}

	// Check the arguments number.
	size_t nargs = 0;
	if (args) nargs = args->list.size;
	if (nargs != f->fn.nargs) {
		panic("function expects %u arguments, got %zu", f->fn.nargs, nargs);
	}

	// Create a new scope for the call.
	// Be careful not to push on stack until the whole scope is done.
	vm.val_t *vargs[100];
	for (size_t i = 0; i < f->fn.nargs; i++) {
		vargs[i] = eval(inter, args->list.items[i]);
	}
	vm.pushscope(inter);
	for (size_t i = 0; i < f->fn.nargs; i++) {
		vm.pushdef(inter, f->fn.argnames[i], vargs[i]);
	}

	// The result of execution will be set here.
	vm.val_t *r = NULL;

	// Reformat the function body to have a better handle on execution
	// and execute each statement.
	vm.val_t **body = vmcomp.compile(inter, f->fn.statements, f->fn.nstatements);
	for (int i = 0; i < TODOSIZE; i++) {
		vm.val_t *x = body[i];

		// No more statements or a special end marker.
		if (!x || is_symbol(x, "__op_end")) {
			break;
		}

		// Conditional jump
		// (__op_test_and_jump_if_false pred)
		if (islist(x, "__op_test_and_jump_if_false")) {
			if (!eval(inter, x->list.items[1])) {
				i += 2; // ok expression + end
			}
			continue;
		}

		// If this is the last statement
		// and a call to the same function,
		// do a tail recursion.
		if ((body[i+1] == NULL || is_symbol(body[i+1], "__op_end"))
			&& x->type == vm.LIST
			&& vm.car(x)->type == vm.SYMBOL
			&& vm.lookup(inter, x->list.items[0]->sym.name) == f
		) {
			// Build a new scope like an new call would produce.
			// It has to be built in isolation and only then added to the stack.
			vm.val_t *newargsv[10];
			vm.val_t *newargs = vm.cdr(inter, x);
			for (size_t i = 0; i < f->fn.nargs; i++) {
				newargsv[i] = eval(inter, newargs->list.items[i]);
			}
			vm.popscope(inter);
			vm.pushscope(inter);
			for (size_t i = 0; i < f->fn.nargs; i++) {
				vm.pushdef(inter, f->fn.argnames[i], newargsv[i]);
			}

			// Start the loop from the beginning with the new scope.
			r = NULL;
			i = -1;
			if (inter->trace) {
				trace_indent(inter->depth);
				printf("TAIL_RECUR: %s\n", f->sym.name);
			}
			continue;
		}

		r = eval(inter, x);
	}

	vm.popscope(inter);
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
	vm.val_t *name = args->list.items[0];
	vm.val_t *val = eval(inter, args->list.items[1]);
	pushdef(inter->stack[0], name->sym.name, val);
	return NULL;
}

vm.val_t *fn_globalget(vm.vm_t *inter, vm.val_t *args) {
	vm.val_t *name = args->list.items[0];
	return vm.globalget(inter, name->sym.name);
}

// (define x const) defines a constant.
// (define (f x) body) defines a function.
vm.val_t *fn_define(vm.vm_t *inter, vm.val_t *args) {
	vm.val_t *name = vm.first(args);

	// (define x const)
	if (name->type == vm.SYMBOL) {
		if (vm.len(args) != 2) {
			panic("constant define requires 2 args, got %zu", vm.len(args));
		}
		vm.val_t *val = vm.second(args);
		vm.pushdef(inter, name->sym.name, eval(inter, val));
		return NULL;
	}

	// (define (twice x) (print x) (foo) (* x 2))
	if (name->type == vm.LIST) {
		const char *fnname = name->list.items[0]->sym.name;
		vm.val_t *defargs = vm.slice(inter, name, 1);
		vm.val_t *defbody = vm.slice(inter, args, 1);
		vm.pushdef(inter, fnname, vm.newfunc(inter, defargs, defbody));
		return NULL;
	}

	vm.dbgprint(args);
	panic("unknown define shape");
}

vm.val_t *fn_cond(vm.vm_t *inter, vm.val_t *args) {
	vm.val_t *l = args;
	while (l) {
		vm.val_t *cas = vm.car(l);
		vm.val_t *cond = eval(inter, vm.car(cas));
		if (truthy(cond)) {
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
	vm.val_t *pred = eval(inter, vm.car(args));
	if (truthy(pred)) {
		vm.val_t *ethen = vm.car(vm.cdr(inter, args));
		return eval(inter, ethen);
	}
	if (args->list.size < 3) {
		return NULL;
	}
	vm.val_t *eelse = vm.car(vm.cdr(inter, vm.cdr(inter, args)));
	return eval(inter, eelse);
}

// (and a b c) returns c if a, b and c are not null.
// Returns null otherwise.
vm.val_t *fn_and(vm.vm_t *inter, vm.val_t *args) {
	for (size_t i = 0; i < args->list.size; i++) {
		if (!eval(inter, args->list.items[i])) {
			return NULL;
		}
	}
	return vm.newsym(inter, "true");
}

// (or a b c) returns the first non-null argument or null.
vm.val_t *fn_or(vm.vm_t *inter, vm.val_t *args) {
	for (size_t i = 0; i < args->list.size; i++) {
		if (eval(inter, args->list.items[i])) {
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
	return eval_func(inter, fn->sym.name, eval(inter, vm.car(vm.cdr(inter, list))));
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
	if (args->list.size == 1) {
		printnum(buf, -atof(a->num.value));
		return vm.newnumber(inter, buf);
	}
	vm.val_t *b = eval(inter, vm.car(vm.cdr(inter, args)));
	if (a->type != vm.NUMBER || b->type != vm.NUMBER) {
		panic("not a number");
	}
	printnum(buf, atof(a->num.value) - atof(b->num.value));
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
	printnum(buf, atof(a->num.value) / atof(b->num.value));
	return vm.newnumber(inter, buf);
}

vm.val_t *fn_numeq(vm.vm_t *inter, vm.val_t *args) {
	vm.val_t *a = eval(inter, vm.car(args));
	vm.val_t *b = eval(inter, vm.car(vm.cdr(inter, args)));
	if (atof(a->num.value) == atof(b->num.value)) {
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
		case vm.SYMBOL: { same = !strcmp(a->sym.name, b->sym.name); }
		case vm.NUMBER: { same = !strcmp(a->num.value, b->num.value); }
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
	if (atof(a->num.value) > atof(b->num.value)) {
		return vm.newsym(inter, "true");
	}
	return NULL;
}

// (< a b) returns true if a < b
vm.val_t *fn_lt(vm.vm_t *inter, vm.val_t *args) {
	vm.val_t *a = eval(inter, vm.car(args));
	vm.val_t *b = eval(inter, vm.car(vm.cdr(inter, args)));
	if (atof(a->num.value) < atof(b->num.value)) {
		return vm.newsym(inter, "true");
	}
	return NULL;
}

// (cons 1 x) constructs a list (1, ...x)
vm.val_t *fn_cons(vm.vm_t *inter, vm.val_t *args) {
	vm.val_t *head = vm.car(args);
	vm.val_t *tail = vm.car(vm.cdr(inter, args));

	vm.val_t *r = vm.newlist(inter);
	r->list.items[r->list.size++] = head;
	for (size_t i = 0; i < tail->list.size; i++) {
		r->list.items[r->list.size++] = tail->list.items[i];
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
	if (args->list.size < 2) {
		panic("want 2 or more arguments");
	}
	double r = start;
	for (size_t i = 0; i < args->list.size; i++) {
		vm.val_t *x = eval(inter, args->list.items[i]);
		if (x->type != vm.NUMBER) {
			panic("not a number");
		}
		double next = atof(x->num.value);
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
	printf("EVAL_SYM %s: ", x->sym.name);
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

bool islist(vm.val_t *x, const char *name) {
	return x->type == vm.LIST
		&& x->list.items[0]->type == vm.SYMBOL
		&& !strcmp(x->list.items[0]->sym.name, name);
}

bool is_symbol(vm.val_t *x, const char *name) {
	return x->type == vm.SYMBOL && !strcmp(x->sym.name, name);
}

bool truthy(vm.val_t *x) {
	return x != NULL && !is_symbol(x, "false");
}
