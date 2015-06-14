-- http://www.youtube.com/watch?v=SQama_q9qtQ&feature=share

module Intro where
open import Level

-- (bottom, the uninhabited type, falsehood)
data ⊥ : Set where

¬ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ A = A → ⊥

notbot : ⊥ → ⊥
notbot ()

data ⊤ : Set where
  tt : ⊤

notnottrue : ¬ ( ¬ ⊤)
notnottrue = λ z → z tt

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor
  _,_
  field
  π₁ : A
  π₂ : B π₁
