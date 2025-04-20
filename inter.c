#import eval.c
#import read.c
#import tok.c
#import tokenizer

pub typedef {
    eval.scope_t *s;
} t;

pub t *new() {
    t *r = calloc(1, sizeof(t));
    if (!r) panic("calloc failed");
    r->s = eval.newscope(NULL);

    // Define standard functions.
    evalstr(r, "(define (abs x) (if (> x 0) x (- x)))");
    return r;
}

pub void free(t *r) {
    OS.free(r->s);
    OS.free(r);
}

pub tok.tok_t *eval(t *inter, tok.tok_t *x) {
    return eval.eval(inter->s, x);
}

pub tok.tok_t *evalstr(t *inter, const char *s) {
    tokenizer.t *b = tokenizer.from_str(s);
	tok.tok_t **all = read.readall(b);
	tokenizer.free(b);

	return eval.evalall(inter->s, all);
}
