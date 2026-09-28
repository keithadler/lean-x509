/* Reads the tab-separated manifest the harness writes: id, leaf, chain (comma-separated), anchor, host. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned char *slurp(const char *dir, const char *name, size_t *len) {
    char path[4096];
    snprintf(path, sizeof path, "%s/%s", dir, name);
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    unsigned char *b = malloc(n > 0 ? n : 1);
    *len = fread(b, 1, n, f);
    fclose(f);
    return b;
}

static void emit(const char *id, int ok, const char *err) {
    if (ok) printf("{\"id\":\"%s\",\"ok\":true}\n", id);
    else printf("{\"id\":\"%s\",\"ok\":false,\"err\":\"%s\"}\n", id, err);
    fflush(stdout);
}

typedef struct { char *id, *leaf, *chain, *anchor, *host; } row;

static int next_row(FILE *f, row *r, char *buf, size_t size) {
    if (!fgets(buf, size, f)) return 0;
    buf[strcspn(buf, "\n")] = 0;
    char *fields[5] = {0};
    char *p = buf;
    for (int i = 0; i < 5; i++) { fields[i] = p; p = strchr(p, '\t'); if (!p) break; *p++ = 0; }
    r->id = fields[0]; r->leaf = fields[1]; r->chain = fields[2]; r->anchor = fields[3]; r->host = fields[4];
    return 1;
}
