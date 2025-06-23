#import strbuilder

pub enum {
	UNKNOWN,
	LIST,
	SYMBOL,
	NUMBER,
};

pub typedef {
	int type;

	// for number:
	char *value;

	// for symbol:
	char *name;

	// for list:
	tok_t **items;
	size_t nitems;
} tok_t;

pub typedef {
	size_t size;
	size_t cap;
	tok_t *items;
} pool_t;

tok_t *make(pool_t *p) {
	if (p->size == p->cap) {
		panic("out of memory");
	}
	tok_t *t = &p->items[p->size++];
	return t;
}

pub tok_t *newnumber(pool_t *p, const char *val) {
	tok_t *t = make(p);
	t->type = NUMBER;
	t->value = calloc(60, 1);
	strcpy(t->value, val);
	return t;
}

pub tok_t *newlist(pool_t *p) {
	tok_t *t = make(p);
	t->type = LIST;
	t->items = calloc(10, sizeof(t));
	return t;
}

pub tok_t *newsym(pool_t *p, const char *s) {
	tok_t *t = make(p);
	t->type = SYMBOL;
	t->name = calloc(60, 1);
	strcpy(t->name, s);
	return t;
}



pub bool islist(tok_t *x, const char *name) {
	return x->type == LIST
		&& x->items[0]->type == SYMBOL
		&& !strcmp(x->items[0]->name, name);
}





// Prints the given item to stdout for debugging.
pub void dbgprint(tok_t *x) {
	char buf[4096];
	if (!x) {
		printf("NULL\n");
		return;
	}
	print(x, buf, 4096);
	printf("%s\n", buf);
}

// Prints the given node into the buf.
pub void print(tok_t *x, char *buf, size_t len) {
	strbuilder.str *s = strbuilder.str_new();
	_print(s, x);
	char *r = strbuilder.str_unpack(s);
	strncpy(buf, r, len);
	free(r);
}

void _print(strbuilder.str *s, tok_t *x) {
	if (!x) {
		strbuilder.adds(s, "NULL");
		return;
	}
	switch (x->type) {
		case SYMBOL: {
			strbuilder.adds(s, x->name);
		}
		case NUMBER: {
			strbuilder.adds(s, x->value);
		}
		case LIST: {
			strbuilder.str_addc(s, '(');
			for (size_t i = 0; i < x->nitems; i++) {
				if (i > 0) {
					strbuilder.str_addc(s, ' ');
				}
				_print(s, x->items[i]);
			}
			strbuilder.str_addc(s, ')');
		}
		default: {
			panic("unknown type");
		}
	}
}
