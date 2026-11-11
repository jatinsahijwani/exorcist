# Exorcist — one-command reproduction. See README.md.
export PATH := $(HOME)/.elan/bin:$(HOME)/.cargo/bin:$(PATH)
MODELS := deposit-vulnerable deposit-fixed noreturn-vulnerable noreturn-fixed withdraw-vulnerable withdraw-fixed
DEPTH ?= 10

.PHONY: demo quick build check prove traces sandbox wasm clean

demo:            ## build, find bugs, check witnesses, prove fixes, sandbox replay, summary
	./scripts/demo.sh

quick:           ## same without the sandbox
	QUICK=1 ./scripts/demo.sh

build:
	lake build

check: build     ## fails if any FIXED model has a violation, or a vulnerable model is not caught
	@for m in deposit-fixed noreturn-fixed withdraw-fixed; do ./.lake/build/bin/exorcist check $$m --depth $(DEPTH) || exit 1; done
	@for m in deposit-vulnerable noreturn-vulnerable withdraw-vulnerable; do ./.lake/build/bin/exorcist check $$m --depth $(DEPTH) >/dev/null; test $$? -eq 1 || { echo "$$m: bug not found"; exit 1; }; done
	@echo "check: fixed models clean (bounded to depth $(DEPTH)); vulnerable models caught"

prove: build
	@for m in deposit-fixed noreturn-fixed withdraw-fixed; do ./.lake/build/bin/exorcist prove $$m || exit 1; done

traces: build    ## export JSON traces for the sandbox
	@for m in $(MODELS); do ./.lake/build/bin/exorcist check $$m --depth $(DEPTH) --json sandbox/traces/$$m.json >/dev/null 2>&1; done; ls sandbox/traces

wasm:
	cd sandbox && ./build-wasm.sh

sandbox: traces wasm
	cd sandbox && cargo test --test replay -- --test-threads=4

clean:
	rm -rf out .lake/build sandbox/target sandbox/res/*.wasm
