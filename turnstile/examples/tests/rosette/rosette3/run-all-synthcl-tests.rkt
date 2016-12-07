#lang racket/base

(require macrotypes/examples/tests/do-tests)

(do-tests
 "synthcl3-tests.rkt" "SynthCL"
 "synthcl3-matrix-synth-tests.rkt" "SynthCL Matrix Mult: synth"
 "synthcl3-matrix-verify-tests.rkt" "SynthCL Matrix Mult: verify"
 "synthcl3-matrix-verify-buggy-tests.rkt" "SynthCL buggy Matrix Mult: verify"
 "synthcl3-walsh-synth-tests.rkt" "SynthCL Walsh Transform: synth" 
 "synthcl3-walsh-verify-tests.rkt" "SynthCL Walsh Transform: verify")
