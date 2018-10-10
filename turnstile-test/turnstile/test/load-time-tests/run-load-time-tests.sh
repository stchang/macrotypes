echo "making"
time raco make turnstile-lang.rkt
time raco make turnstile-base-lang.rkt

echo "with racket: --------------------"

echo "racket-base-prog.rkt"
time racket racket-base-prog.rkt
echo "racket-prog.rkt"
time racket racket-prog.rkt
echo "turnstile-base-lang.rkt"
time racket turnstile-base-lang.rkt
echo "turnstile-lang.rkt"
time racket turnstile-lang.rkt
echo "turnstile-base-lang-prog.rkt"
time racket turnstile-base-lang-prog.rkt
echo "turnstile-lang-prog.rkt"
time racket turnstile-lang-prog.rkt

echo "with raco test: --------------------"

echo "racket-base-prog.rkt"
time raco test racket-base-prog.rkt
echo "racket-prog.rkt"
time raco test racket-prog.rkt
echo "turnstile-base-lang.rkt"
time raco test turnstile-base-lang.rkt
echo "turnstile-lang.rkt"
time raco test turnstile-lang.rkt
echo "turnstile-base-lang-prog.rkt"
time raco test turnstile-base-lang-prog.rkt
echo "turnstile-lang-prog.rkt"
time raco test turnstile-lang-prog.rkt
