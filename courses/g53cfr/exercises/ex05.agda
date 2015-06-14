{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Thorsten Altenkirch

  Exercise 5: Arithmetic
  Deadline: 5/3/2010, 12:00

  Use the coursework submission (id: 271)) system to submit the coursework
  after demonstrating it in the lab to me or Darin.
  
  Prove the following propositions of propositional logic by
  completing the sheds { .. }.

  Note that not all propositions may be provable. If you think that a
  proposition is unprovable clearly mark this one by adding a line:
  -- impossible.

  You may want to prove some auxilliary lemmas.
-}

module ex05 where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary -- Dec
open ≡-Reasoning
open import Data.Product
open import Data.Sum
{- we use ⊎ (\uplus) for ∨ -}
open import Algebra
module ℕ = CommutativeSemiring Data.Nat.Properties.commutativeSemiring

{- This structure shows that ℕ is a commutative semiring, e.g.
   ℕ.+-comm : m + n ≡ n + m
   ℕ.+-assoc : (m + n) + l ≡ m + (n + l)
   ℕ.*-comm : m * n ≡ n * m
   ℕ.*-assoc : (m * n) * l ≡ m * (n * l)
   ℕ.distribʳ : (y + z) * x ≡ y * x + z * x
-}

{- Warm up: I define doubling: -}

2*_ : ℕ → ℕ
2* zero = 0
2* suc n = 2 + 2* n

{- prove it is the same as adding a number to itself: -}

2*Lem : (m : ℕ) → 2* m ≡ m + m
2*Lem m = {!!}

{- Define functions,
   mod₂ : remainder of division by 2
   div₂ : division by two 
-}
mod₂ : ℕ → ℕ 
mod₂ m = {!!}

div₂ : ℕ → ℕ
div₂ m = {!!}

{- And prove the following properties: -}

mod₂Lem : (n : ℕ) → mod₂ n ≡ 0 ⊎ mod₂ n ≡ 1
mod₂Lem n = {!!}

div₂Lem : (n : ℕ) → 2 * (div₂ n) + mod₂ n ≡ n
div₂Lem n = {!!}

{- Show that equality modulo 2 is decidable. -}

_≡₂_ : ℕ → ℕ → Set
m ≡₂ n = mod₂ m ≡ mod₂ n

_≡₂?_ : (m n : ℕ) → Dec (m ≡₂ n)
m ≡₂? n = {!!}


