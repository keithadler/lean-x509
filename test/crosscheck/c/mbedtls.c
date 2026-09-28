/* mbedTLS 4: parse leaf and intermediates into one chain, verify against the anchor for the host name
   (at the current time: mbedTLS has no way to set it), then the serverAuth EKU. */
#include "common.h"
#include <mbedtls/x509_crt.h>
#include <psa/crypto.h>

int main(int argc, char **argv) {
    const char *dir = argv[1];
    char path[4096], buf[8192];
    psa_crypto_init();
    snprintf(path, sizeof path, "%s/manifest.tsv", dir);
    FILE *m = fopen(path, "r");
    row r;
    while (next_row(m, &r, buf, sizeof buf)) {
        mbedtls_x509_crt chain, trust;
        mbedtls_x509_crt_init(&chain);
        mbedtls_x509_crt_init(&trust);
        char err[256] = "";
        size_t len;
        unsigned char *b = slurp(dir, r.leaf, &len);
        int ret = mbedtls_x509_crt_parse_der(&chain, b, len);
        free(b);
        if (ret) snprintf(err, sizeof err, "parse leaf: -0x%04x", -ret);
        char *names = strdup(r.chain);
        for (char *n = strtok(names, ","); !*err && n; n = strtok(NULL, ",")) {
            b = slurp(dir, n, &len);
            ret = mbedtls_x509_crt_parse_der(&chain, b, len);
            free(b);
            if (ret) snprintf(err, sizeof err, "parse intermediate: -0x%04x", -ret);
        }
        free(names);
        if (!*err) {
            b = slurp(dir, r.anchor, &len);
            ret = mbedtls_x509_crt_parse_der(&trust, b, len);
            free(b);
            if (ret) snprintf(err, sizeof err, "parse anchor: -0x%04x", -ret);
        }
        if (!*err) {
            uint32_t flags = 0;
            ret = mbedtls_x509_crt_verify(&chain, &trust, NULL, r.host, &flags, NULL, NULL);
            if (ret) snprintf(err, sizeof err, "verify: -0x%04x flags 0x%08x", -ret, flags);
        }
        if (!*err && mbedtls_x509_crt_check_extended_key_usage(&chain, "\x2b\x06\x01\x05\x05\x07\x03\x01", 8))
            snprintf(err, sizeof err, "extKeyUsage does not allow serverAuth");
        emit(r.id, !*err, err);
        mbedtls_x509_crt_free(&chain);
        mbedtls_x509_crt_free(&trust);
    }
    return 0;
}
