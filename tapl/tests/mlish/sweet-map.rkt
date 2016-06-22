#lang sweet-exp "../../typed-lang-builder/mlish-core.rkt"

define
  sum [lst : (List Int)] → Int
  match lst with
    [] -> 0
    x :: xs ->
      {x + sum(xs)}

define
  map [f : (→ X Y)] [lst : (List X)] → (List Y)
  match lst with
    [] -> nil
    x :: xs ->
      cons
        f x
        map f xs

sum
  map string->number (list "1" "2" "3")
