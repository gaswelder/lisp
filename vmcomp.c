#import vm.c

#define TODOSIZE 100
#define TODOVOIDPSIZE 64

bool TRACE = false;

pub vm.val_t **compile(vm.vm_t *p, vm.val_t **in, size_t n) {
    if (TRACE) {
        printf("compile:\n");
        for (size_t i = 0; i < n; i++) {
            vm.dbgprint(in[i]);
        }
    }

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

    if (TRACE) {
        printf("result:\n");
        for (int i = 0; i < pos; i++) {
            printf("%d: ", i);
            vm.dbgprint(out[i]);
        }
    }

	return out;
}

int compile_if(vm.vm_t *p, vm.val_t *x, vm.val_t *body[], int added) {
	// Tests the condition and skips the ok branch if false.
	vm.val_t *tst = vm.newlist(p);
	tst->list.items[tst->list.size++] = vm.globalget(p, "__test_and_jump_if_false");
	tst->list.items[tst->list.size++] = x->list.items[1];
	body[added++] = tst;

	// The ok branch with an end marker.
	body[added++] = x->list.items[2];
	body[added++] = vm.globalget(p, "__end");

	// The else branch.
	body[added++] = x->list.items[3];

	return added;
}

int compile_cond(vm.vm_t *p, vm.val_t *cond, vm.val_t *body[], int added) {
	for (size_t i = 1; i < cond->list.size; i++) {
		vm.val_t *alt = cond->list.items[i];

		// Tests the condtion and skips the ok expression if false.
		// Implies that cond values have exactly one expression.
		vm.val_t *tst = vm.newlist(p);
		tst->list.items[tst->list.size++] = vm.globalget(p, "__test_and_jump_if_false");
		tst->list.items[tst->list.size++] = alt->list.items[0];
		body[added++] = tst;

		// Value followed by the stop command
		// (implies that this cond is the last expression)
		body[added++] = alt->list.items[1];
		body[added++] = vm.globalget(p, "__end");
	}
	return added;
}

bool islist(vm.val_t *x, const char *name) {
	return x->type == vm.LIST
		&& x->list.items[0]->type == vm.SYMBOL
		&& !strcmp(x->list.items[0]->sym.name, name);
}
