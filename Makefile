.PHONY: install-all install-turnstile install-turnstile-test

install-all: install-turnstile install-turnstile-test

install-turnstile:
	raco pkg install --auto macrotypes-lib/
	raco pkg install --auto turnstile-lib/

install-turnstile-test:
	raco pkg install --auto rackunit-macrotypes-lib/
	raco pkg install --auto turnstile-example/
	raco pkg install --auto turnstile-test/
