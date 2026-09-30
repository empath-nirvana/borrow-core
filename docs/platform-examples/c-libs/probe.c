/* Probe: two C libraries, built with wasi-sdk for wasm32-wasip2 and linked into one component.
 *
 * - zlib: a compress/uncompress round trip through caller-owned buffers, the shape of a
 *   borrow-for-the-call FFI contract (in: an `imm` view; out: a `mut` view and a count).
 * - BearSSL: a TLS client engine. It does no I/O of its own: it hands out records to send and
 *   takes records received, so our own TCP capability can carry them (route 2 of §6).
 */
#include <stdio.h>
#include <string.h>
#include "zlib.h"
#include "bearssl.h"
#include <unistd.h>   /* getentropy: wasi:random on WASI, the OS on POSIX */

int main(void) {
    const char *msg = "{\"type\":\"ADDED\",\"object\":{\"metadata\":{\"name\":\"m0\"}}}\n"
                      "{\"type\":\"ADDED\",\"object\":{\"metadata\":{\"name\":\"m1\"}}}\n";
    unsigned char packed[256], unpacked[256];
    uLongf plen = sizeof packed, ulen = sizeof unpacked;
    int z1 = compress(packed, &plen, (const Bytef *)msg, strlen(msg));
    int z2 = uncompress(unpacked, &ulen, packed, plen);
    printf("zlib %s: %zu -> %lu -> %lu bytes, round trip %s\n", zlibVersion(), strlen(msg),
           (unsigned long)plen, (unsigned long)ulen,
           z1 == Z_OK && z2 == Z_OK && ulen == strlen(msg) && !memcmp(unpacked, msg, ulen)
               ? "ok" : "FAILED");

    static br_ssl_client_context cc;
    static br_x509_minimal_context xc;
    static unsigned char iobuf[BR_SSL_BUFSIZE_BIDI];
    br_ssl_client_init_full(&cc, &xc, NULL, 0);   /* trust anchors: none in this probe */
    br_ssl_engine_set_buffer(&cc.eng, iobuf, sizeof iobuf, 1);
    /* BearSSL 0.6 has no entropy source for this target: without a seed, reset fails with
     * BR_ERR_NO_RANDOM. The seed must come from the platform, which is authority the C
     * library would otherwise take ambiently. */
    int reset0 = br_ssl_client_reset(&cc, "kubernetes.default.svc", 0);
    printf("bearssl: reset without a seed %d, error %d (BR_ERR_NO_RANDOM = %d)\n", reset0,
           br_ssl_engine_last_error(&cc.eng), BR_ERR_NO_RANDOM);
    unsigned char seed[32];
    if (getentropy(seed, sizeof seed) != 0) return 1;
    br_ssl_engine_inject_entropy(&cc.eng, seed, sizeof seed);
    int reset = br_ssl_client_reset(&cc, "kubernetes.default.svc", 0);
    unsigned st = br_ssl_engine_current_state(&cc.eng);
    size_t n = 0;
    if (st & BR_SSL_SENDREC) br_ssl_engine_sendrec_buf(&cc.eng, &n);
    printf("bearssl: reset %d, state %s, ClientHello record of %zu bytes ready for our socket\n",
           reset, (st & BR_SSL_SENDREC) ? "SENDREC" : "other", n);
    return 0;
}
