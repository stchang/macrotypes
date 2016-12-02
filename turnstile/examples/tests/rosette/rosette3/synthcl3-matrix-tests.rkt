#lang s-exp "../../../rosette/synthcl3.rkt"
(require "../../rackunit-typechecking.rkt"
         (prefix-in cl: sdsl/synthcl/lang/main)
         (prefix-in ro: (rename-in rosette [#%app a])))

; The reference implementation for square matrix multiplication.  
; Multiplies two squre matrices A and B, where the dimension of A is 
; n x p and dimension of B is p x m.  Both matrices are given as 
; flat arrays in row-major form.  The output is the matrix C = A*B, 
; also given in row-major form. 
(procedure int* (mmulSequential [int* A] [int* B] [int n] [int p] [int m])
  (: int* C)
  (= C ((int*) (malloc (* n m (sizeof int)))))
  (for [(: int i in (range n))
        (: int j in (range m))
        (: int k in (range p))]
        (+= [C (+ (* i m) j)] (* [A (+ (* i p) k)] [B (+ (* k m) j)])))
  C)

; A host implementation of matrix multiplication.
(procedure int* (mmulHost [char* kernelName] [int typeLen] 
                          [int* A] [int* B] [int n] [int p] [int m])
  (: cl_context context)
  (: cl_command_queue command_queue)
  (: cl_program program)
  (: cl_kernel kernel)
  (: cl_mem buffer_A buffer_B buffer_C)

  (: int* C)
  (: int[2] global)
  (: int dimA dimB dimC)
  (= [global 0] (/ n typeLen))
  (= [global 1] (/ m typeLen))
  (= dimA (* n p (sizeof int))) 
  (= dimB (* p m (sizeof int))) 
  (= dimC (* n m (sizeof int)))
  
  (= C ((int*) (malloc dimC)))
  
  (= context (clCreateContext))
  
  (= command_queue (clCreateCommandQueue context))
 
  (= buffer_A (clCreateBuffer context CL_MEM_READ_ONLY dimA))
  (= buffer_B (clCreateBuffer context CL_MEM_READ_ONLY dimB))
  (= buffer_C (clCreateBuffer context CL_MEM_WRITE_ONLY dimC))
  
  (= program (clCreateProgramWithSource context "matrix-synth-kernel.rkt"))
  
  (clEnqueueWriteBuffer command_queue buffer_A 0 dimA A)
  (clEnqueueWriteBuffer command_queue buffer_B 0 dimB B)
  
  (= kernel (clCreateKernel program kernelName))
  (clSetKernelArg kernel 0 buffer_A)
  (clSetKernelArg kernel 1 buffer_B)
  (clSetKernelArg kernel 2 buffer_C)
  (clSetKernelArg kernel 3 p)
  (clSetKernelArg kernel 4 m)

  (clEnqueueNDRangeKernel command_queue kernel 2 NULL global NULL)
  (clEnqueueReadBuffer command_queue buffer_C 0 dimC C)
  C)
; A scalar parallel implementation of matrix multiplication.
(procedure int* (mmulScalar [int* A] [int* B] [int n] [int p] [int m])
  (mmulHost "mmulScalarKernel" 1 A B n p m))

; A vector parallel implementation of matrix multiplication.  The dimensions 
; n and m must be evenly divisible by 4.
(procedure int* (mmulVector [int* A] [int* B] [int n] [int p] [int m])
  (mmulHost "mmulVectorKernel" 4 A B n p m))

; Given two arrays of the same size, checks that they hold the same 
; values at each index.
(procedure void (check [int* actual] [int* expected] [int SIZE])
  (assert (>= SIZE 0))
  (for [(: int i in (range SIZE))]
    (assert (== [actual i] [expected i]))))

(procedure void (synth_vector [int size])
  (synth #:forall [(: int n in (range size (+ 1 size)))
                   (: int p in (range size (+ 1 size)))
                   (: int m in (range size (+ 1 size)))      
                   (: int[(* n p)] A) 
                   (: int[(* p m)] B)] 
         #:ensure (check (mmulVector A B n p m) 
                         (mmulSequential A B n p m)
                         (* n m))))

(: int n)
(= n 4)
(: int p)
(= p 4)
(: int m)
(= m 4)
(: int[(* n p)] A) 
(: int[(* p m)] B)
(check-type (mmulVector A B n p m) : int*)
(check-type (mmulSequential A B n p m) : int*)

(check-type
 (with-output-to-string
   (λ ()
     (synth_vector 4))) ; 20 sec
     : CString
     -> "/home/stchang/NEU_Research/macrotypes/turnstile/examples/tests/rosette/rosette3/matrix-synth-kernel.rkt:57:0\n'(procedure\n  int\n  (indexA (int off) (int i) (int k) (int p))\n  (: int r c w)\n  (= r (+ (choose i (/ i 4) (* i 4)) off))\n  (= c (+ (choose k (/ k 4) (* k 4)) 0))\n  (= w (+ (/ p 4) 0))\n  (+ (* r w) c))\n/home/stchang/NEU_Research/macrotypes/turnstile/examples/tests/rosette/rosette3/matrix-synth-kernel.rkt:66:0\n'(procedure\n  int\n  (indexB (int off) (int k) (int j) (int m))\n  (: int r c w)\n  (= r (+ (choose k (/ k 4) (* k 4)) off))\n  (= c (+ (choose j (/ j 4) (* j 4)) 0))\n  (= w (+ (/ m 4) 0))\n  (+ (* r w) c))\n/home/stchang/NEU_Research/macrotypes/turnstile/examples/tests/rosette/rosette3/matrix-synth-kernel.rkt:75:0\n'(procedure\n  int\n  (indexC (int off) (int i) (int j) (int m))\n  (: int r c w)\n  (= r (+ (choose i (/ i 4) (* i 4)) off))\n  (= c (+ (choose j (/ j 4) (* j 4)) 0))\n  (= w (+ (/ m 4) 0))\n  (+ (* r w) c))\n")
;(synth_vector 8) ; 252 sec
