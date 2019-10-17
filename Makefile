# Turnstile+ Makefile

install: turnstile+ turnstile+-examples

turnstile+:
	raco pkg install -D --auto -t dir macrotypes-lib/ turnstile-lib/

turnstile+-examples:
	raco pkg install -D --auto -t dir rackunit-macrotypes-lib/ turnstile-example/ turnstile-test/

test:
	raco test -j 4 turnstile-test/tests/popl2020/*.rkt

remove:
	raco pkg remove --auto turnstile-test turnstile-example rackunit-macrotypes-lib turnstile-lib macrotypes-lib
