#import tokenizer
#import vm.c

pub vm.val_t **readall(vm.vm_t *p, const char *s) {
    tokenizer.t *b = tokenizer.from_str(s);
	vm.val_t **all = calloc(100, sizeof(b));
	size_t n = 0;
	while (true) {
		vm.val_t *t = readtok(p, b);
		if (!t) break;
		all[n++] = t;
	}
    tokenizer.free(b);
	return all;
}

// Reads next item.
pub vm.val_t *readtok(vm.vm_t *p, tokenizer.t *b) {
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
