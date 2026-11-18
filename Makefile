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

.PHONY: bcc run tools gate gate-full gate-full-nocache gate-full-record gate-fast gate-daily goldens keys verify-goldens bench

# Build the `bcc` compiler.
bcc: $(CACHE_STAMP) | tools
	lake build bcc
	@echo "built $(BCC)"

# Compile a program to WebAssembly by Backend2, the default backend, and run it under wasmtime
# (`make run -- --backend old <file.bc>` for the old backend).
run: bcc
	$(BCC) run $(RUN_ARGS)

# The per-PR gate (scripts/ci-local.sh): the steps the change's tier names (scripts/gate-tier.sh,
# from the paths changed since the merge base with origin/main), each on every program or on the
# programs the change touches, with the result cache. It prints the tier at the top and with its
# verdict; what it leaves out runs in the daily full gate on main (scripts/gate-daily.sh).
gate: | tools
	scripts/ci-local.sh

# The full gate: every check (every compiled stage, counts, native, the static tables, the
# generated and renamed programs, the book), the source stage on the unverified goldens of the
# corpus and the book, with the result cache. Run by `make gate` itself when the tier is `full`.
gate-full: | tools
	scripts/ci-local.sh --full

# The full gate with every unit run, the result cache (scripts/gate_cache.py) neither read nor
# written.
gate-full-nocache: | tools
	scripts/ci-local.sh --full --no-cache

# The full gate with every unit run and its passes recorded, none replayed: the daily run on main,
# which re-establishes every result and fills the result cache for that day's main.
gate-full-record: | tools
	scripts/ci-local.sh --full --record-cache

# The daily full gate on main (scripts/gate-daily.sh): `make gate-full` without the result cache
# on origin/main in a checkout of its own, its verdict posted to the board for the coordinator.
# Does nothing when origin/main already has a verdict. Run by launchd (scripts/gate-daily.plist).
gate-daily:
	scripts/gate-daily.sh

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

# The required tools are on PATH, and shared packages follow the manifest and toolchain
# (scripts/lake-packages.sh).
tools:
	@command -v lean >/dev/null || { echo "lean not found: run 'brew bundle', and add ~/.elan/bin to PATH"; exit 1; }
	@command -v lake >/dev/null || { echo "lake not found: run 'brew bundle', and add ~/.elan/bin to PATH"; exit 1; }
	@command -v wasmtime >/dev/null || { echo "wasmtime not found: run 'brew bundle'"; exit 1; }
	@scripts/lake-packages.sh check

# Resolve dependencies and fetch prebuilt Mathlib, again only when the pins change.
$(CACHE_STAMP): lake-manifest.json lean-toolchain | tools
	lake exe cache get
	@mkdir -p $(@D)
	@touch $@
