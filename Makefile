.PHONY: install install-turnstile install-examples test
.PHONY: uninstall forced-uninstall

R=raco
RI=$(R) pkg install
IFLAGS=--auto
RT=$(R) test
TFLAGS=-j 4
RR=$(R) pkg remove

install: install-turnstile install-examples

install-turnstile:
	$(RI) $(IFLAGS) -t dir macrotypes-lib/ turnstile-lib/

install-examples:
	$(RI) $(IFLAGS) -t dir rackunit-macrotypes-lib/ turnstile-example/ turnstile-test/

test:
	$(RT) $(TFLAGS) -p turnstile-test

uninstall: # must be separate cmds, in case one fails
	-$(RR) --auto turnstile-test
	-$(RR) --auto turnstile-example
	-$(RR) --auto macrotypes-test
	-$(RR) --auto turnstile-example
	-$(RR) --auto macrotypes-example
	-$(RR) --auto turnstile-doc
	-$(RR) --auto rackunit-macrotypes-lib
	-$(RR) --auto turnstile-lib
	-$(RR) --auto macrotypes-lib

forced-uninstall:
	-$(RR) --force turnstile-test
	-$(RR) --force turnstile-example
	-$(RR) --force macrotypes-test
	-$(RR) --force turnstile-example
	-$(RR) --force macrotypes-example
	-$(RR) --force turnstile-doc
	-$(RR) --force rackunit-macrotypes-lib
	-$(RR) --force turnstile-lib
	-$(RR) --force macrotypes-lib
