.PHONY: build test axioms

build:
	lake build LeanTLS LeanTLS.Tests.RFC8448 LeanTLS.Tests.Handshake

test: build
	lake exe LeanTLS.Tests.RFC8448
	lake exe LeanTLS.Tests.Handshake

axioms: build
	scripts/check-axioms.sh

testdata/rfc8448_1rtt.json: ## regenerate from the RFC text: make testdata/rfc8448_1rtt.json RFC8448=path/to/rfc8448.txt
	python3 -I scripts/extract_rfc8448.py $(RFC8448) > $@
	sha256sum $@ > $@.sha256
