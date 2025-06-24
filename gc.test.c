#import inter.c
// #import test

int main() {
    inter.t *in = inter.new(400);
    for (size_t i = 0; i < 100; i++) {
        inter.evalstr(in, "123");
    }
    printmem(in);
    inter.gc(in);
    printmem(in);
    inter.gc(in);
    printmem(in);


    for (size_t i = 0; i < 300; i++) {
        printf("%zu\n", i);
        inter.evalstr(in, "123");
        printmem(in);
    }
    // printmem(in);


    inter.free(in);
    return 0;
}

void printmem(inter.t *in) {
    for (size_t i = 0; i < in->poolsize; i++) {
        if (i > 0 && i % 50 == 0) printf("\n");
        printf("%d", in->in_use[i]);
    }
    printf("\n\n");
}
