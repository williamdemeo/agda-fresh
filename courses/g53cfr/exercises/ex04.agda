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
∃∨-lem-1 = {!!}

∃∨-lem-2 : {A : Set}{P Q : A → Prp} → (∃ A λ a → P a) ∨ (∃ A λ a → Q a) 
           ⇒ (∃ A λ a → P a ∨ Q a) 
∃∨-lem-2 = {!!}

∃∨-lem : {A : Set}{P Q : A → Prp} → 
       (∃ A λ a → P a ∨ Q a) ⇔ (∃ A λ a → P a) ∨ (∃ A λ a → Q a)
∃∨-lem = {!!}

∀∀com : {A B : Set}{R : A → B → Prp} →
      ∀' A (λ a → ∀' B (λ b → R a b)) ⇒ ∀' B (λ b → ∀' A (λ a → R a b))
∀∀com = {!!}

∃∃com : {A B : Set}{R : A → B → Prp} →
      ∃ A (λ a → ∃ B (λ b → R a b)) ⇒ ∃ B (λ b → ∃ A (λ a → R a b))
∃∃com = {!!}

∀∃com : {A B : Set}{R : A → B → Prp} →
      ∀' A (λ a → ∃ B (λ b → R a b)) ⇒ ∃ B (λ b → ∀' A (λ a → R a b))
∀∃com = {!!}

∃∀com : {A B : Set}{R : A → B → Prp} →
       ∃ B (λ b → ∀' A (λ a → R a b)) ⇒ ∀' A (λ a → ∃ B (λ b → R a b))
∃∀com = {!!}

deMorgan¬∃ : {A : Set}{P : A → Prp} →
           ¬ (∃ A (λ x → P x)) ⇒ ∀' A (λ x → ¬ (P x))
deMorgan¬∃ = {!!}

deMorgan∀¬ : {A : Set}{P : A → Prp} →
           ∀' A (λ x → ¬ (P x)) ⇒ ¬ (∃ A (λ x → P x))
deMorgan∀¬ = {!!}

deMorgan¬∀ : {A : Set}{P : A → Prp} →
             ¬ (∀' A (λ x → P x)) ⇒ ∃ A (λ x → ¬ (P x))
deMorgan¬∀ = {!!}

deMorgan∃¬ : {A : Set}{P : A → Prp} →
           ∃ A (λ x → ¬ (P x)) ⇒ ¬ (∀' A (λ x → P x))
deMorgan∃¬ = {!!}

