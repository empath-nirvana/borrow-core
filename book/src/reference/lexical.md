# Lexical structure

{{#include ../../../docs/syntax-core.md:lexical}}

Further details from the parser (`Frontend/README.md`):

- Integer literals are decimal or `0x`/`0X` hexadecimal, with no sign and no separators. The
  types `1` and `0` are the integer tokens `1` and `0`.
- A decimal with a fraction or an exponent (`1.5`, `2.5e-3`, `1e10`) is a float literal of the
  surface; the core writes a float by its bits, `f64[n]` (SPEC §37). `b'c'` is a byte, and `"…"`
  a string literal (SPEC §17).
- `-o` is one token even before a letter, and `--` starts a comment everywhere.
- Only the Unicode spellings in the table above are accepted (no `→`, `⇒`).
- Keywords, constant names, `val`, `block`, `leaf`, `node`, `str` and `main` are reserved as
  lower-case names; `U`, `F` and `Fun` as upper-case names.
