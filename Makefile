# Developer entry points. Tools come from the Brewfile (`brew bundle`); the Lean version is
# pinned by `lean-toolchain` and fetched by elan.

BCC := .lake/build/bin/bcc
# Records that the Mathlib cache matches the current manifest and toolchain.
CACHE_STAMP := .lake/cache.stamp

# `make run <file.bc> [args]` passes the words after `run` to `bcc run`. Each
# word is also a goal, so it gets an empty phony rule. Arguments starting with `-` go after `--`
# (`make run -- --flag prog.bc`) so make does not read them as its own options.
ifeq (run,$(firstword $(MAKECMDGOALS)))
  RUN_ARGS := $(wordlist 2,$(words $(MAKECMDGOALS)),$(MAKECMDGOALS))
  $(if $(RUN_ARGS),,$(error usage: make run <file.bc>))
  .PHONY: $(RUN_ARGS)
  $(eval $(RUN_ARGS):;@:)
endif

.PHONY: bcc run tools gate gate-full gate-fast goldens keys verify-goldens bench

# Build the `bcc` compiler.
bcc: $(CACHE_STAMP) | tools
	lake build bcc
	@echo "built $(BCC)"

# Compile a program to WebAssembly by Backend2, the default backend, and run it under wasmtime
# (`make run -- --backend old <file.bc>` for the old backend).
run: bcc
	$(BCC) run $(RUN_ARGS)

# The sanity gate (scripts/ci-local.sh): the build, hygiene and axioms, the judgment freeze and
# the Backend2 fence, the type-equality census, the corpus parsed, checked and renamed, and every corpus program run in WebAssembly by
# each backend against its golden with `live 0` (Backend2, the default, and the old backend until
# N7); the source stage only on unverified goldens (scripts/source-stage.sh: no recorded key, or
# not the current one).
gate: | tools
	scripts/ci-local.sh

# The full gate: every check (every compiled stage, counts, native, the static tables, the
# generated and renamed programs, the book), the source stage on the unverified goldens of the
# corpus and the book. Required when Paper/, Support/, Target/, Pipeline/, Reference/ or Backend/
# changed.
gate-full: | tools
	scripts/ci-local.sh --full

# Re-verify every golden: the source stage on every corpus program and book block (with each
# compiled to WebAssembly), whatever its key. Writes no key.
verify-goldens: | tools
	scripts/compile-corpus.sh --source --final
	scripts/book-doctest.sh --source

# While iterating: the sanity gate's steps the changes since origin/main reach, never the source
# stage.
gate-fast: | tools
	scripts/ci-local.sh --changed

# The benchmarks against Rust and C (bench/README.md): build each (ours by Backend2, or with
# `BENCH_ARGS="--backend old"` by the old backend), time it, write the table to
# bench/out/results.md. Not part of the gate. `make bench BENCH_ARGS="--only sum --runs 5"`.
bench: bcc
	python3 bench/bench.py $(BENCH_ARGS)

# Rewrite every corpus golden (`.out`, `.err`, `.status`) from `Support`'s interpreter, with its
# key (`.key`).
goldens: | tools
	scripts/compile-corpus.sh --write-goldens

# Record the key of every unverified golden the source stage verifies (corpus `<name>.key`,
# book/keys/), running it on exactly those (scripts/source-stage.sh).
keys: | tools
	scripts/compile-corpus.sh --final --write-keys
	scripts/book-doctest.sh --write-keys

# The required tools are on PATH.
tools:
	@command -v lean >/dev/null || { echo "lean not found: run 'brew bundle', and add ~/.elan/bin to PATH"; exit 1; }
	@command -v lake >/dev/null || { echo "lake not found: run 'brew bundle', and add ~/.elan/bin to PATH"; exit 1; }
	@command -v wasmtime >/dev/null || { echo "wasmtime not found: run 'brew bundle'"; exit 1; }

# Resolve dependencies and fetch prebuilt Mathlib, again only when the pins change.
$(CACHE_STAMP): lake-manifest.json lean-toolchain | tools
	lake exe cache get
	@mkdir -p $(@D)
	@touch $@
