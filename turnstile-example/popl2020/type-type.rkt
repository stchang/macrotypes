#lang turnstile+

;; An implementation of Type : Type

(provide Type (for-syntax ~Type))

(require turnstile+/typedefs)

(define-type Type : Type)
