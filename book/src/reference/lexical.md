# Lexical structure

{{#include ../../../docs/syntax-core.md:lexical}}

Further details from the parser (`Frontend/README.md`):

- Integer literals are decimal or `0x`/`0X` hexadecimal, with no sign and no separators. The
  types `1` and `0` are the integer tokens `1` and `0`.
- `-o` is one token even before a letter, and `--` starts a comment everywhere.
- Only the Unicode spellings in the table above are accepted (no `→`, `⇒`).
- Keywords, constant names, `val`, `block`, `leaf`, `node`, `str` and `main` are reserved as
  lower-case names; `U`, `F` and `Fun` as upper-case names.
