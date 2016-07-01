bg
===

mlish tests by Ben

`basics-general`
---
```
(map [f : (→ A B)] [x* : (List A)] → (List B))
(append [x* : (List A)] [y* : (List A)] → (List A))
(fst [xy : (** A B)] → A)
(snd [xy : (** A B)] → B)
(member [x* : (List A)] [y : A] → Bool)
(foldl [f : (→ A B A)] [acc : A] [x* : (List B)] → A)
(foldr [f : (→ A B B)] [x* : (List A)] [acc : B] → B)
(filter [f : (→ A Bool)] [x* : (List A)] → (List A))
(sum [x* : (List Float)] → Float)
(reverse [x* : (List A)] → (List A))
```

`basics`
---
```
(fn-list [f* : (List (→ A A))] [a : A] → A)
(count-letters/one [s : String] [c : Char] → Int)
(count-letters [s* : (List String)] [c : Char] → Int)
(flatten [x** : (List (List A))] → (List A))
(insert [x : A] → (→ (List A) (List (List A))))
(permutations [x* : (List A)] → (List (List A)))
(split [ab* : (List (** A B))] → (** (List A) (List B)))
(combine [a*b* : (** (List A) (List B))] → (List (** A B)))
(convolve [x* : (List Float)] [y* : (List Float)] → Float)
(mc [n : Int] [f : (→ A A)] [x : A] → A)
(square [n : Int] → Int)
(successor [mcn : (→ (→ A A) A A)] → (→ (→ A A) A A))
(split2 [x* : (List A)] → (** (List A) (List A)))
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

`basics2`
---
```
(map-index [is* : (List (** Int (List String)))] → (List (** String Int)))
(reduce-index [si* : (List (** String Int))] → (List (** String (List Int))))
(make-index [is* : (List (** Int (List String)))] → (List (** String (List Int))))
```

`huffman`
---
```
(empty → Symbol*)
(singleton [s : String] → Symbol*)
(insert [s* : Symbol*] [s1 : String] → Symbol*)
(union [s1 : Symbol*] [s2 : Symbol*] → Symbol*)
(contains [s* : Symbol*] [s : Symbol] → Bool)
(list [x : A] → (List A))
(append [x* : (List A)] [y* : (List A)] → (List A))
(length [x* : (List A)] → Int)
(symbols [h : HTree] → Symbol*)
(weight [h : HTree] → Int)
(make-code-tree [left : HTree] [right : HTree] → HTree)
(decode-aux [bits : Bit*] [root : HTree] [current-branch : HTree] → SymbolList)
(decode [bits : Bit*] [tree : HTree] → SymbolList)
(choose-branch [bit : Bit] [branch : HTree] → HTree)
(adjoin-set [x : HTree] [set : HTreeSet] → HTreeSet)
(make-leaf-set [pair* : (List (× Symbol Int))] → HTreeSet)
sample-tree
sample-message
(encode [message : SymbolList] [tree : HTree] → Bit*)
(contains-symbol [s : Symbol] [tree : HTree] → Bool)
(encode-symbol [s : Symbol] [tree : HTree] → Bit*)
(generate-huffman-tree [pair* : (List (× Symbol Frequency))] → HTree)
(successive-merge [tree* : HTreeSet] → HTree)
rock-pair*
rock-tree (generate-huffman-tree rock-pair*))
rock-message
rock-bit* (encode rock-message rock-tree))
```


`lambda`
---
```
(fresh [e : Λ] → Int)
(subst [e : Λ] [i : Int] [v : Λ] → Λ)
(simpl-aux [e : Λ] [i : Int] → (× Int Λ))
(simpl [e : Λ] → Λ)
(eval [e : Λ] → Λ)
I (Lambda 0 (Var 0))
K (Lambda 0 (Lambda 1 (Var 0)))
S (Lambda 0 (Lambda 1 (Lambda 2 (App (App (Var 0) (Var 2)) (App (Var 1) (Var 2))))))
false (App S K)
```
