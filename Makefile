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

.PHONY: bcc run tools

# Build the `bcc` compiler.
bcc: $(CACHE_STAMP) | tools
	lake build bcc
	@echo "built $(BCC)"

# Compile a program to WebAssembly and run it under wasmtime.
run: bcc
	$(BCC) run $(RUN_ARGS)

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
