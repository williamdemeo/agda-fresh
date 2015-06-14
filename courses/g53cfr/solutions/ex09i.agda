module ex09i where

open import Data.Maybe
open import Data.List
open import Data.Nat
open import Data.Product

data Order : Set where le gt : Order

order : ℕ → ℕ → Order
order zero n = le
order (suc m) zero = gt
order (suc m) (suc n) = order m n

data Tree (A : Set) : Set where
  node : Tree A → A → Tree A → Tree A
  leaf : Tree A

insert : ℕ → Tree ℕ → Tree ℕ
insert n (node l m r) with order n m
... | le = node (insert n l) m r
... | gt = node l m (insert n r)
insert n leaf = node leaf n leaf

flatten : {A : Set} → Tree A → List A 
flatten (node l n r) = flatten l ++ (n ∷ flatten r)
flatten leaf = []

insertAll : List ℕ → Tree ℕ
insertAll [] = leaf
insertAll (n ∷ ns) = insert n (insertAll ns) 

sort : List ℕ → List ℕ 
sort xs = flatten (insertAll xs)

ex1 : List ℕ
ex1 = 5 ∷ 2 ∷ 0 ∷ 1 ∷ 4 ∷ 3 ∷ []

ex2 : List ℕ
ex2 = 100 ∷ 1 ∷ 10 ∷ 1 ∷ 100 ∷ 10 ∷ []


