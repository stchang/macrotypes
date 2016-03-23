bg
===

mlish tests by Ben

`basics`
---
```
(fn-list [f* : (List (→ A A))] [a : A] → A)
(count-letters/one [s : String] [c : Char] → Int)
(count-letters [s* : (List String)] [c : Char] → Int)
(map [f : (→ A B)] [x* : (List A)] → (List B))
(append [x* : (List A)] [y* : (List A)] → (List A))
(flatten [x** : (List (List A))] → (List A))
(insert [x : A] → (→ (List A) (List (List A))))
(permutations [x* : (List A)] → (List (List A)))
(split [ab* : (List (** A B))] → (** (List A) (List B)))
(combine [a*b* : (** (List A) (List B))] → (List (** A B)))
(fst [xy : (** A B)] → A)
(snd [xy : (** A B)] → B)
(member [x* : (List A)] [y : A] → Bool)
(foldl [f : (→ A B A)] [acc : A] [x* : (List B)] → A)
(foldr [f : (→ A B B)] [x* : (List A)] [acc : B] → B)
(filter [f : (→ A Bool)] [x* : (List A)] → (List A))
(sum [x* : (List Float)] → Float)
(reverse [x* : (List A)] → (List A))
(convolve [x* : (List Float)] [y* : (List Float)] → Float)
(mc [n : Int] [f : (→ A A)] [x : A] → A)
(square [n : Int] → Int)
(successor [mcn : (→ (→ A A) A A)] → (→ (→ A A) A A))
(map-index [is* : (List (** Int (List String)))] → (List (** String Int)))
(reduce-index [si* : (List (** String Int))] → (List (** String (List Int))))
(make-index [is* : (List (** Int (List String)))] → (List (** String (List Int))))
(split [x* : (List A)] → (** (List A) (List A)))
(merge [x*+y* : (** (List Int) (List Int))] → (List Int))
(mergesort {x* : (List Int)} → (List Int))
(quicksort [x* : (List Int)] → (List Int))
(fact [n : Int] → Int)
(range-aux [n : Int] → (List Int))
(range [n : Int] → (List Int))
(fact-acc [n : Int] → Int)
(fact-cps-aux [n : Int] [k : (→ Int Int)] → Int)
(fact-cps [n : Int] → Int)
(map-cps-aux [f : (→ A B)] [x* : (List A)] [k : (→ (List B) (List B))] → (List B))
(map-cps [f : (→ A B)] [x* : (List A)] → (List B))
```


