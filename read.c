#import tokenizer
#import tok.c

pub tok.tok_t **readall(tok.pool_t *p, tokenizer.t *b) {
	tok.tok_t **all = calloc(100, sizeof(b));
	size_t n = 0;
	while (true) {
		tok.tok_t *t = read(p, b);
		if (!t) break;
		all[n++] = t;
	}
	return all;
}

// Reads next item from the buffer.
pub tok.tok_t *read(tok.pool_t *p, tokenizer.t *b) {
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
tok.tok_t *readnum(tok.pool_t *p, tokenizer.t *b) {
	char buf[100];
	if (!tokenizer.num(b, buf, 100)) {
		panic("failed to read a number");
	}
	return tok.newnumber(p, buf);
}

// Reads a symbol.
tok.tok_t *readsymbol(tok.pool_t *p, tokenizer.t *b) {
	tok.tok_t *t = tok.newsym(p, "");
	int pos = 0;
	while (tokenizer.more(b) && !isspace(tokenizer.peek(b)) && tokenizer.peek(b) != ')') {
		t->name[pos++] = tokenizer.get(b);
	}
	if (pos == 0) {
		panic("failed to read symbol at %s", tokenizer.posstr(b));
	}
	return t;
}


// Reads a list.
tok.tok_t *readlist(tok.pool_t *p, tokenizer.t *b) {
	tok.tok_t *t = tok.newlist(p);

	tokenizer.get(b); // "("
	tokenizer.spaces(b);
	while (tokenizer.peek(b) != EOF && tokenizer.peek(b) != ')') {
		t->items[t->nitems++] = read(p, b);
		tokenizer.spaces(b);
	}
	if (tokenizer.peek(b) != ')') {
		panic("expected )");
	}
	tokenizer.get(b); // ")"
	return t;
}
