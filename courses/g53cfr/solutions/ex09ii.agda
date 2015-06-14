module ex09ii where

open import Algebra
open import Data.Maybe
open import Data.Vec
open import Data.Nat
open import Data.Product
open import Data.Nat.Properties
private
  module ℕ = CommutativeSemiring commutativeSemiring
open import Relation.Binary.PropositionalEquality
import Algebra.RingSolver.AlmostCommutativeRing as ACR
import Algebra.RingSolver.Simple as Solver

open Solver (ACR.fromCommutativeSemiring commutativeSemiring)

zeroLem : (n : ℕ) → n ≡ n + 0
zeroLem = solve 1 (\n → n := n :+ con 0) refl 

sucLem₁ : (m n : ℕ) → (1 + (m + n)) ≡ (m + (1 + n))
sucLem₁ = solve 2 (\m n → con 1 :+ (m :+ n) := m :+ (con 1 :+ n)) refl

sucLem₂ : (m n : ℕ) → (m + (1 + n)) ≡ (1 + (m + n)) 
sucLem₂ m n = sym (sucLem₁ m n)   

data Order : Set where le gt : Order

order : ℕ → ℕ → Order
order zero n = le
order (suc m) zero = gt
order (suc m) (suc n) = order m n

data Tree (A : Set) : ℕ → Set where
  node : ∀ {m n} → Tree A m → A → Tree A n → Tree A (m + (1 + n))
  leaf : Tree A 0

insert : ∀ {n} → ℕ → Tree ℕ n → Tree ℕ (1 + n)
insert n (node {sl} {sr} l m r) with order n m
... | le = node (insert n l) m r
... | gt = subst (\n → Tree ℕ n) (sucLem₂ sl (1 + sr)) (node l m (insert n r))  
insert n leaf = node leaf n leaf

flatten : {A : Set} {n : ℕ} → Tree A n → Vec A n 
flatten (node l n r) = flatten l ++ (n ∷ flatten r)
flatten leaf = []

insertAll : ∀ {n} → Vec ℕ n → Tree ℕ n
insertAll [] = leaf
insertAll (n ∷ ns) =  insert n (insertAll ns)  

sort : ∀ {n} → Vec ℕ n → Vec ℕ n 
sort xs = flatten (insertAll xs) 

ex1 : Vec ℕ 6
ex1 = 5 ∷ 2 ∷ 0 ∷ 1 ∷ 4 ∷ 3 ∷ []

ex2 : Vec ℕ 6
ex2 = 100 ∷ 1 ∷ 10 ∷ 1 ∷ 100 ∷ 10 ∷ []


