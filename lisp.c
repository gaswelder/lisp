#import inter.c

int main(int argc, char *argv[]) {
	FILE *f = NULL;
	switch (argc) {
		case 1: { f = stdin; }
		case 2: {
			f = fopen(argv[1], "r");
			if (!f) {
				fprintf(stderr, "failed to open %s\n", argv[1]);
				return 1;
			}
		}
		default: {
			fprintf(stderr, "arguments: [<file>]\n");
			return 1;
		}
	}
	inter.tt_t *in = inter.new(400000);
	return inter.repl(in, f);
}
