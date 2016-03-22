bg
===

mlish tests by Ben

- `ps1` : 
  ```
  (define (fn-list [f* : (List (→ A A))] [a : A] → A)
  (define (count-letters/one [s : String] [c : Char] → Int)
  (define (count-letters [s* : (List String)] [c : Char] → Int)
  (define (map [f : (→ A B)] [x* : (List A)] → (List B))
  (define (append [x* : (List A)] [y* : (List A)] → (List A))
  (define (flatten [x** : (List (List A))] → (List A))
  (define (insert [x : A] → (→ (List A) (List (List A))))
  (define (permutations [x* : (List A)] → (List (List A)))
  (define (split [ab* : (List (** A B))] → (** (List A) (List B)))
  (define (combine [a*b* : (** (List A) (List B))] → (List (** A B)))
  (define (fst [xy : (** A B)] → A)
  (define (snd [xy : (** A B)] → B)
  (define (foldl [f : (→ A B A)] [acc : A] [x* : (List B)] → A)
  (define (sum [x* : (List Float)] → Float)
  (define (reverse [x* : (List A)] → (List A))
  (define (convolve [x* : (List Float)] [y* : (List Float)] → Float)
  (define (mc [n : Int] [f : (→ A A)] [x : A] → A)
  (define (square [n : Int] → Int)
  (define (successor [mcn : (→ (→ A A) A A)] → (→ (→ A A) A A))
  ```
- 
