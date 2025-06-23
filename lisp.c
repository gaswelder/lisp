#import tokenizer
#import inter.c

int main(int argc, char *argv[]) {
	tokenizer.t *b = NULL;
	switch (argc) {
		case 1: { b = tokenizer.stdin(); }
		case 2: {
			FILE *f = fopen(argv[1], "r");
			if (!f) {
				fprintf(stderr, "failed to open %s\n", argv[1]);
				return 1;
			}
			b = tokenizer.file(f);
		}
		default: {
			fprintf(stderr, "arguments: [<file>]\n");
			return 1;
		}
	}

	char buf[4096];
	inter.t *in = inter.new();
	while (true) {
		// Read a form.
		inter.tok_t *x = inter.readtok(in, b);
		if (!x) break;

		// Echo.
		printf("> ");
		inter.print(x, buf, 4096);
		puts(buf);

		// Evaluate and print.
		inter.tok_t *r = inter.eval(in, x);
		if (!inter.islist(x, "define")) {
			inter.print(r, buf, 4096);
			puts(buf);
		}
	}

	// printf("%zu\n", in->poolsize);
	return 0;
}
