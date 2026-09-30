#!/bin/sh
# Builds zlib 1.3.1 and BearSSL 0.6 with wasi-sdk for wasm32-wasip2, links probe.c against both
# into one component, and runs it. WASI_SDK is the unpacked wasi-sdk (tested: wasi-sdk-34).
#
#   WASI_SDK=/path/to/wasi-sdk-34.0-arm64-macos docs/platform-examples/c-libs/build.sh
set -e
: "${WASI_SDK:?set WASI_SDK to an unpacked wasi-sdk}"
here=$(cd "$(dirname "$0")" && pwd)
work=${WORK:-$(mktemp -d)}
cd "$work"
[ -d zlib-1.3.1 ] || curl -sL https://github.com/madler/zlib/releases/download/v1.3.1/zlib-1.3.1.tar.gz | tar xz
[ -d bearssl-0.6 ] || curl -sL https://www.bearssl.org/bearssl-0.6.tar.gz | tar xz
CC="$WASI_SDK/bin/clang --target=wasm32-wasip2 -O2"
mkdir -p obj
for f in $(find bearssl-0.6/src -name '*.c'); do
  $CC -Ibearssl-0.6/inc -Ibearssl-0.6/src -c "$f" -o "obj/bearssl_$(echo "$f" | tr / _).o"
done
for f in adler32 compress crc32 deflate inflate inftrees inffast trees uncompr zutil; do
  $CC -c "zlib-1.3.1/$f.c" -o "obj/z_$f.o"
done
"$WASI_SDK/bin/ar" rcs libbearssl.a obj/bearssl_*.o
"$WASI_SDK/bin/ar" rcs libz.a obj/z_*.o
$CC -Izlib-1.3.1 -Ibearssl-0.6/inc "$here/probe.c" libz.a libbearssl.a -o c-libs.wasm
echo "imports of the component:"
wasm-tools component wit c-libs.wasm | grep '^  import'
wasmtime run c-libs.wasm
