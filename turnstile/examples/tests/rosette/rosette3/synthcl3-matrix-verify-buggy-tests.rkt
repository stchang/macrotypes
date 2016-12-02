#lang s-exp "../../../rosette/synthcl3.rkt"
(require "../../rackunit-typechecking.rkt")

; A buggy reference implementation for square matrix multiplication.  
; Multiplies two squre matrices A and B, where the dimension of A is 
; n x p and dimension of B is p x m.  Both matrices are given as 
; flat arrays in row-major form.  The output is the matrix C = A*B, 
; also given in row-major form. 
(procedure int* (mmulSequential [int* A] [int* B] [int n] [int p] [int m])
  (: int* C)
  (= C ((int*) (malloc (* n m (sizeof int)))))
  (for [(: int i in (range n))
        (: int j in (range m))
        (: int k in (range 1 p))] ; seeded bug
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
  
  (= program (clCreateProgramWithSource context "matrix-verify-kernel.rkt"))
  
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

; An optimized vector parallel implementation of matrix multiplication.  The dimensions 
; n and m must be evenly divisible by 4.
(procedure int* (mmulVectorOpt [int* A] [int* B] [int n] [int p] [int m])
  (mmulHost "mmulVectorKernelOpt" 4 A B n p m))

; Given two arrays of the same size, checks that they hold the same 
; values at each index.
(procedure void (check [int* actual] [int* expected] [int SIZE])
  (assert (>= SIZE 0))
  (for [(: int i in (range SIZE))]
    (assert (== [actual i] [expected i]))))

(procedure void (verify_scalar [int from] [int to])
  (verify #:forall [(: int n in (range from to))
                    (: int p in (range from to))
                    (: int m in (range from to))
                    (: int[(* n p)] A) 
                    (: int[(* p m)] B)] 
          #:ensure (check (mmulScalar A B n p m) 
                          (mmulSequential A B n p m)
                          (* n m))))

(procedure void (verify_vector [int from] [int to])
  (verify #:forall [(: int n in (range from to 4))
                    (: int p in (range from to 4))
                    (: int m in (range from to 4))       
                    (: int[(* n p)] A) 
                    (: int[(* p m)] B)] 
          #:ensure (check (mmulVector A B n p m) 
                          (mmulSequential A B n p m)
                          (* n m))))

(procedure void (verify_vector_opt [int from] [int to])
  (verify #:forall [(: int n in (range from to 4))
                    (: int p in (range from to 4))
                    (: int m in (range from to 4))       
                    (: int[(* n p)] A) 
                    (: int[(* p m)] B)] 
          #:ensure (check (mmulVectorOpt A B n p m) 
                          (mmulSequential A B n p m)
                          (* n m))))
(check-type
 (with-output-to-string (λ () (verify_scalar 1 5)))
 : CString -> "counterexample found:\nn = 1\np = 1\nm = 1\nA = #x0#(-1)\nB = #x1#(1)\n")
(check-type
 (with-output-to-string (λ () (verify_vector 4 9)))
 : CString -> "counterexample found:\nn = 4\np = 4\nm = 4\nA = #x5#(3 0 0 0 3 0 0 0 98355 0 0 0 98307 0 0 0)\nB = #x6#(-1431655765 -1431655765 1431661227 0 0 0 0 0 0 0 0 0 0 0 0 0)\n")
(check-type
 (with-output-to-string (λ () (verify_vector_opt 4 9)))
 : CString -> "counterexample found:\nn = 4\np = 4\nm = 4\nA = #xa#(3 0 0 0 3 0 0 0 98355 0 0 0 98307 0 0 0)\nB = #xb#(-1431655765 -1431655765 1431661227 0 0 0 0 0 0 0 0 0 0 0 0 0)\n")

;(: int n p m)
;(= n 8) (= p 4) (= m 4)
;(: int[(* n p)] A) (: int[(* p m)] B)
;(mmulVector A B n p m)


