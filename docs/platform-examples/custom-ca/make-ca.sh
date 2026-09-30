#!/bin/sh
# A private CA and a server certificate for localhost signed by it, as a cluster CA signs the
# API server's certificate. Output in the directory given (default ./pki).
set -e
d=${1:-pki}; mkdir -p "$d"; cd "$d"
openssl req -x509 -newkey rsa:2048 -nodes -keyout ca.key -out ca.crt -days 2 \
  -subj "/CN=probe-cluster-ca" -addext "basicConstraints=critical,CA:TRUE" \
  -addext "keyUsage=critical,keyCertSign,cRLSign" 2>/dev/null
openssl req -newkey rsa:2048 -nodes -keyout server.key -out server.csr -subj "/CN=localhost" 2>/dev/null
printf 'subjectAltName=DNS:localhost,IP:127.0.0.1\nextendedKeyUsage=serverAuth\nbasicConstraints=CA:FALSE\n' > ext.cnf
openssl x509 -req -in server.csr -CA ca.crt -CAkey ca.key -CAcreateserial -out server.crt \
  -days 2 -extfile ext.cnf 2>/dev/null
printf 'probe-token-123' > token
echo "wrote $d/ca.crt $d/server.crt $d/server.key $d/token"
