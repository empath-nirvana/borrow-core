"""A local stand-in for the Kubernetes API server: HTTPS with a certificate signed by a private
CA, a bearer token check, and a chunked body of JSON lines (a watch stream).

    python3 server.py <cert.pem> <key.pem> <token> [port]
"""
import http.server, ssl, sys, time

CERT, KEY, TOKEN = sys.argv[1], sys.argv[2], sys.argv[3]
PORT = int(sys.argv[4]) if len(sys.argv) > 4 else 8443


class H(http.server.BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def do_GET(self):
        if self.headers.get("Authorization") != "Bearer " + TOKEN:
            self.send_response(401)
            self.send_header("Content-Length", "0")
            self.end_headers()
            return
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Transfer-Encoding", "chunked")
        self.end_headers()
        for i in range(3):
            line = ('{"type":"ADDED","object":{"metadata":{"name":"m%d"}}}\n' % i).encode()
            self.wfile.write(b"%x\r\n%s\r\n" % (len(line), line))
            self.wfile.flush()
            time.sleep(0.2)
        self.wfile.write(b"0\r\n\r\n")

    def log_message(self, *a):
        pass


ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
ctx.load_cert_chain(CERT, KEY)
srv = http.server.HTTPServer(("127.0.0.1", PORT), H)
srv.socket = ctx.wrap_socket(srv.socket, server_side=True)
srv.serve_forever()
