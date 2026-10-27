.PHONY: build test axioms bench

build:
	lake build LeanTLS LeanTLS.Tests.RFC8448 LeanTLS.Tests.Handshake

test: build
	lake exe LeanTLS.Tests.RFC8448
	lake exe LeanTLS.Tests.Handshake

axioms: build
	scripts/check-axioms.sh

# Extra LeanBench flags, e.g. `make bench BENCH_ARGS='--where "name(/ML-DSA/)" --samples 5'`.
BENCH_ARGS ?=

# The benchmarks are their own Lake project in bench/, so the library does not depend on LeanBench.
bench:
	@cd bench && lake -q --log-level=error exe lean_tls-bench $(BENCH_ARGS)

testdata/rfc8448_1rtt.json: ## regenerate from the RFC text: make testdata/rfc8448_1rtt.json RFC8448=path/to/rfc8448.txt
	python3 -I scripts/extract_rfc8448.py $(RFC8448) > $@
	sha256sum $@ > $@.sha256
