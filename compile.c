#import tok.c

#define TODOSIZE 100
#define TODOVOIDPSIZE 64

pub tok.tok_t **compile(tok.tok_t **in, size_t n) {
	tok.tok_t **out = calloc(TODOSIZE, TODOVOIDPSIZE);
	int pos = 0;

	for (size_t i = 0; i < n; i++) {
		tok.tok_t *x = in[i];

		// Flatten tail ifs so the interpreter can attempt a tail recursion.
		if (i == n - 1 && tok.islist(x, "if")) {
			pos = compile_if(x, out, pos);
			continue;
		}
		if (i == n - 1 && tok.islist(x, "cond")) {
			pos = compile_cond(x, out, pos);
			continue;
		}
		out[pos++] = x;
	}

	return out;
}

int compile_if(tok.tok_t *x, tok.tok_t *body[], int added) {
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

int compile_cond(tok.tok_t *cond, tok.tok_t *body[], int added) {
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
