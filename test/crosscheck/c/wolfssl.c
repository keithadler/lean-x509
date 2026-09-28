/* wolfSSL, through its OpenSSL-compatible X509_STORE: the anchor is the only trusted certificate, the
   intermediates are an untrusted stack, and the time is the corpus time. Then the host name and the
   serverAuth EKU. */
#include "common.h"
#include <wolfssl/options.h>
#include <wolfssl/ssl.h>
#include <wolfssl/openssl/x509v3.h>

static WOLFSSL_X509 *load(const char *dir, const char *name) {
    size_t len;
    unsigned char *b = slurp(dir, name, &len);
    if (!b) return NULL;
    const unsigned char *p = b;
    WOLFSSL_X509 *x = wolfSSL_d2i_X509(NULL, &p, (int)len);
    free(b);
    return x;
}

int main(int argc, char **argv) {
    const char *dir = argv[1];
    char path[4096], buf[8192];
    wolfSSL_Init();
    snprintf(path, sizeof path, "%s/now.txt", dir);
    FILE *t = fopen(path, "r");
    long now = 0;
    if (fscanf(t, "%ld", &now) != 1) return 2;
    fclose(t);
    snprintf(path, sizeof path, "%s/manifest.tsv", dir);
    FILE *m = fopen(path, "r");
    row r;
    while (next_row(m, &r, buf, sizeof buf)) {
        char err[256] = "";
        WOLFSSL_X509 *leaf = load(dir, r.leaf), *anchor = load(dir, r.anchor);
        WOLF_STACK_OF(WOLFSSL_X509) *untrusted = wolfSSL_sk_X509_new_null();
        if (!leaf) snprintf(err, sizeof err, "d2i refused the leaf");
        if (!*err && !anchor) snprintf(err, sizeof err, "d2i refused the anchor");
        char *list = strdup(r.chain);
        for (char *n = strtok(list, ","); !*err && n; n = strtok(NULL, ",")) {
            WOLFSSL_X509 *x = load(dir, n);
            if (!x) snprintf(err, sizeof err, "d2i refused intermediate %s", n);
            else wolfSSL_sk_X509_push(untrusted, x);
        }
        free(list);
        if (!*err) {
            WOLFSSL_X509_STORE *store = wolfSSL_X509_STORE_new();
            wolfSSL_X509_STORE_add_cert(store, anchor);
            WOLFSSL_X509_STORE_CTX *ctx = wolfSSL_X509_STORE_CTX_new();
            wolfSSL_X509_STORE_CTX_init(ctx, store, leaf, untrusted);
            wolfSSL_X509_STORE_CTX_set_time(ctx, 0, (time_t)now);
            if (wolfSSL_X509_verify_cert(ctx) != 1)
                snprintf(err, sizeof err, "verify: error %d", wolfSSL_X509_STORE_CTX_get_error(ctx));
            wolfSSL_X509_STORE_CTX_free(ctx);
            wolfSSL_X509_STORE_free(store);
        }
        if (!*err && wolfSSL_X509_check_host(leaf, r.host, strlen(r.host), 0, NULL) != 1)
            snprintf(err, sizeof err, "host name does not match");
        if (!*err) {
            unsigned int xku = wolfSSL_X509_get_extended_key_usage(leaf);
            if (xku != 0xFFFFFFFF && xku != 0 && !(xku & XKU_SSL_SERVER))
                snprintf(err, sizeof err, "extKeyUsage does not allow serverAuth");
        }
        emit(r.id, !*err, err);
        wolfSSL_sk_X509_pop_free(untrusted, wolfSSL_X509_free);
        if (leaf) wolfSSL_X509_free(leaf);
        if (anchor) wolfSSL_X509_free(anchor);
    }
    return 0;
}
