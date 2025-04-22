#import tokenizer
#import read.c
#import tok.c
#import inter.c

int main() {
	char buf[4096];
	inter.t *in = inter.new();

	tokenizer.t *b = tokenizer.stdin();
	while (true) {
		// Read a form.
		tok.tok_t *x = read.read(b);
		if (!x) break;

		// Echo.
		printf("> ");
		tok.print(x, buf, 4096);
		puts(buf);

		// Evaluate and print.
		tok.tok_t *r = inter.eval(in, x);
		if (!tok.islist(x, "define")) {
			tok.print(r, buf, 4096);
			puts(buf);
		}
	}
	return 0;
}
