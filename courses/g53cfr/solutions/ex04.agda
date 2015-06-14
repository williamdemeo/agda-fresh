{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Thorsten Altenkirch

  Exercise 4: Predicate Logic (19/2/09)
  Deadline: 26/2/09, 12:00

  Use the coursework submission (id: 267)) system to submit the coursework
  after demonstrating it in the lab to me or Darin.
  
  Prove the following propositions of predicate logic by
  completing the sheds { .. }.

  Note that not all propositions may be provable. If you think that a
  proposition is unprovable clearly mark this one by adding a line:
  -- impossible.

-}

module ex04 where

open import l05
open import l06
open import l07

∃∨-lem-1 : {A : Set}{P Q : A → Prp} → (∃ A λ a → P a ∨ Q a) 
           ⇒ (∃ A λ a → P a) ∨ (∃ A λ a → Q a)
∃∨-lem-1 (a , d) with d 
∃∨-lem-1 (a , d) | left  pa  = left  (a , pa)
∃∨-lem-1 (a , d) | right qa  = right (a , qa)

∃∨-lem-2 : {A : Set}{P Q : A → Prp} → (∃ A λ a → P a) ∨ (∃ A λ a → Q a) 
           ⇒ (∃ A λ a → P a ∨ Q a) 
∃∨-lem-2 (left  (a , pa)) = a , left  pa
∃∨-lem-2 (right (a , qa)) = a , right qa

∃∨-lem : {A : Set}{P Q : A → Prp} → 
       (∃ A λ a → P a ∨ Q a) ⇔ (∃ A λ a → P a) ∨ (∃ A λ a → Q a)
∃∨-lem = ∃∨-lem-1 , ∃∨-lem-2

∀∀com : {A B : Set}{R : A → B → Prp} →
      ∀' A (λ a → ∀' B (λ b → R a b)) ⇒ ∀' B (λ b → ∀' A (λ a → R a b))
∀∀com f b a = f a b -- same as flip

∃∃com : {A B : Set}{R : A → B → Prp} →
      ∃ A (λ a → ∃ B (λ b → R a b)) ⇒ ∃ B (λ b → ∃ A (λ a → R a b))
∃∃com (a , (b , p)) = b , (a , p)

∀∃com : {A B : Set}{R : A → B → Prp} →
      ∀' A (λ a → ∃ B (λ b → R a b)) ⇒ ∃ B (λ b → ∀' A (λ a → R a b))
∀∃com = {!!}
-- impossible. Take A = B = {0,1} and R the equality on {0,1}. Then ∀a ∃b a=b but we don't have ∃b∀a a=b because 0≠1.
-- This argument can be carried out in Agda, here using {false, true} instead of {0, 1}:
data Bool : Set where
  false : Bool
  true  : Bool

not : Bool → Bool
not true  = false
not false = true

¬[notb≢b] : (b : Bool) → not b  ≡ b → ⊥
¬[notb≢b] true ()
¬[notb≢b] false ()

∀a∃b-a≡b : ∀' Bool (λ a → ∃ Bool (λ b → a ≡ b))
∀a∃b-a≡b a = (a , refl)

¬∀∃com[Bool,≡] : ¬(∀' Bool (λ a → ∃ Bool (λ b → a ≡ b)) ⇒ ∃ Bool (λ b → ∀' Bool (λ a → a ≡ b)))
¬∀∃com[Bool,≡] h with h ∀a∃b-a≡b
...              | (b , f) = ¬[notb≢b] b (f (not b))

-- This refutes the second order statement that for all sets A, B and relation R we have ∀∃com {A} {B} {R}.

-- We can then derive ⊥ from ∀∃com. Therefore ∀∃com is not provable, as ⊥ is not provable.
FALSE : ⊥
FALSE = ¬∀∃com[Bool,≡] ∀∃com



∃∀com : {A B : Set}{R : A → B → Prp} →
       ∃ B (λ b → ∀' A (λ a → R a b)) ⇒ ∀' A (λ a → ∃ B (λ b → R a b))
∃∀com ( b , f) a = b , f a

deMorgan¬∃ : {A : Set}{P : A → Prp} →
           ¬ (∃ A (λ x → P x)) ⇒ ∀' A (λ x → ¬ (P x))
deMorgan¬∃ ne a pa = ne (a , pa)

deMorgan∀¬ : {A : Set}{P : A → Prp} →
           ∀' A (λ x → ¬ (P x)) ⇒ ¬ (∃ A (λ x → P x))
deMorgan∀¬ f (a , pa) = f a pa

deMorgan¬∀ : {A : Set}{P : A → Prp} →
             ¬ (∀' A (λ x → P x)) ⇒ ∃ A (λ x → ¬ (P x))
deMorgan¬∀ = {!!}
-- Impossible, else we could define deMorgan¬∧ as follows, but it is not definable (lecture 5).

if₁ : {P Q : Prp} → Bool → Prp
if₁ {P} {Q} true  = P
if₁ {P} {Q} false = Q

deMorgan¬∧ : {P Q : Prp} → ¬ (P ∧ Q) ⇒ (¬ P) ∨ (¬ Q)
deMorgan¬∧ npq with deMorgan¬∀ {Bool} {if₁} (λ y → npq (y true , y false))  
...                    | true  , np = left  np
...                    | false , nq = right nq

deMorgan∃¬ : {A : Set}{P : A → Prp} →
           ∃ A (λ x → ¬ (P x)) ⇒ ¬ (∀' A (λ x → P x))
deMorgan∃¬ (a , npa) f = npa (f a)

