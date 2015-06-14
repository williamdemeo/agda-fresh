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

2*Lem : ∀ {m} → 2* m ≡ m + m
2*Lem {zero} = refl
2*Lem {suc m} = begin 
  2* (suc m)    ≡⟨ refl ⟩
  2 + 2* m      ≡⟨ cong (_+_ 2) (2*Lem {m}) ⟩
  2 + (m + m)   ≡⟨ cong suc (ℕ.+-comm (suc m) m) ⟩
  suc m + suc m
  ∎

{- Define functions,
   mod₂ : remainder of division by 2
   div₂ : division by two 
-}
mod₂ : ℕ → ℕ 
mod₂ zero = 0
mod₂ (suc zero) = 1
mod₂ (suc (suc n)) = mod₂ n

div₂ : ℕ → ℕ
div₂ zero = zero
div₂ (suc zero) = zero
div₂ (suc (suc n)) = suc (div₂ n)

{- And prove the following properties: -}

mod₂Lem : (n : ℕ) → mod₂ n ≡ 0 ⊎ mod₂ n ≡ 1
mod₂Lem zero = inj₁ refl
mod₂Lem (suc zero) = inj₂ refl
mod₂Lem (suc (suc n)) = mod₂Lem n

s2* : ∀{n} → 2 * (suc n) ≡ 2 + 2 * n
s2* {n} =  begin 
  2 * (suc n) ≡⟨ ℕ.*-comm 2 (suc n) ⟩
  (suc n) * 2 ≡⟨ refl ⟩
  2 + n * 2 ≡⟨ cong (_+_ 2) (ℕ.*-comm n 2) ⟩
  2 + 2 * n
  ∎

div₂Lem : ∀ {n} → 2 * (div₂ n) + mod₂ n ≡ n
div₂Lem {zero} = refl
div₂Lem {suc zero} = refl
div₂Lem {suc (suc n)} = begin 
  2 * div₂ (suc (suc n)) + mod₂ (suc (suc n))    ≡⟨ refl ⟩
  2 * suc (div₂ n) + mod₂ n    ≡⟨ cong (λ x → x + mod₂ n) (s2* {div₂ n}) ⟩
  2 + (2 * div₂ n + mod₂ n)    ≡⟨ cong (_+_ 2) div₂Lem ⟩
  suc (suc n)
  ∎

{- Show that equality modulo 2 is decidable. -}

_≡₂_ : ℕ → ℕ → Set
m ≡₂ n = mod₂ m ≡ mod₂ n

_≡₂?_ : (m n : ℕ) → Dec (m ≡₂ n)
zero ≡₂? zero = yes refl
zero ≡₂? suc zero = no (λ ())
zero ≡₂? suc (suc n) = zero ≡₂? n
suc zero ≡₂? zero = no (λ ())
suc zero ≡₂? suc zero = yes refl
suc zero ≡₂? suc (suc n) = suc zero ≡₂? n
suc (suc n) ≡₂? n' = n ≡₂? n'

