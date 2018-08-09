echo "racket racket-base-prog.rkt"
time racket racket-base-prog.rkt
echo "racket racket-prog.rkt"
time racket racket-prog.rkt
time raco test racket-base-prog.rkt
time raco test racket-prog.rkt
echo "racket turnstile-lang.rkt"
time racket turnstile-lang.rkt
echo "racket turnstile-lang-prog.rkt"
time racket turnstile-lang-prog.rkt
time raco test turnstile-lang.rkt
time raco test turnstile-lang-prog.rkt

