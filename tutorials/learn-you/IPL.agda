-- Based on the tutorial "Learn You an Agda"

module IPL where

  data nat : Set where
    zero : nat
    suc : nat -> nat

  _+_ : nat -> nat -> nat
  zero + n = n
  (suc n) + m = suc (n + m)

  data _even : nat -> Set where
    ZERO : zero even
    STEP : forall x -> x even -> suc (suc x) even

  proof1 : suc (suc (suc (suc zero))) even 
  proof1 = STEP (suc (suc zero)) (STEP zero ZERO)

  proof2 : nat -> nat
  proof2 n = n

  proof2' : (A : Set) -> A -> A
  proof2' _ x = x


  data _∧_ (P : Set) (Q : Set) : Set where
    ∧-intro : P → Q → (P ∧ Q)

  proof₃ : {P Q : Set} → (P ∧ Q) → P
  proof₃ (∧-intro p q) = p

  proof₄ : {P Q : Set} → (P ∧ Q) → Q
  proof₄ (∧-intro p q) = q

  _⇔_ : (P : Set) → (Q : Set) → Set
  a ⇔ b = (a → b) ∧ (b → a)
  
  ∧-comm′ : {P Q : Set} → (P ∧ Q) → (Q ∧ P)
  ∧-comm′ (∧-intro p q) = ∧-intro q p

  ∧-comm : {P Q : Set} → (P ∧ Q) ⇔ (Q ∧ P)
  ∧-comm = ∧-intro ∧-comm′ ∧-comm′

  ∧-assoc₁ : { P Q R : Set } → ((P ∧ Q) ∧ R) → (P ∧ (Q ∧ R))
  ∧-assoc₁ (∧-intro (∧-intro p q) r) = ∧-intro p (∧-intro q r)

  ∧-assoc₂ : { P Q R : Set } → (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R)
  ∧-assoc₂ (∧-intro p (∧-intro q r)) = ∧-intro (∧-intro p q) r

  ∧-assoc : { P Q R : Set } → ((P ∧ Q) ∧ R) ⇔  (P ∧ (Q ∧ R))
  ∧-assoc = ∧-intro ∧-assoc₁ ∧-assoc₂

  data _∨_ (P Q : Set) : Set where
    ∨-intro₁ : P → P ∨ Q
    ∨-intro₂ : Q → P ∨ Q

  data ⊥ : Set where
