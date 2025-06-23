pub typedef {
    size_t size;
    uint8_t *bytes;
} t;

pub t *new(size_t n) {
    t *s = calloc(1, sizeof(t));
    if (!s) panic("calloc failed");
    s->bytes = calloc(n, 1);
    if (!s->bytes) panic("calloc failed");
    s->size = n;
    return s;
}

void check_bounds(t *s, size_t i) {
    if (i >= s->size) {
        panic("size out of bounds: %zu > %zu", i, s->size);
    }
}

pub void set(t *s, size_t i) {
    printf("set %zu\n", i);
    check_bounds(s, i);
    s->bytes[i] = 1;
}

pub void unset(t *s, size_t i) {
    check_bounds(s, i);
    s->bytes[i] = 0;
}

pub bool isset(t *s, size_t i) {
    check_bounds(s, i);
    return s->bytes[i];
}

pub void free(t *s) {
    OS.free(s);
}
