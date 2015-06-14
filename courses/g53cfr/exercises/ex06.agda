{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Thorsten Altenkirch

  Exercise 6: Inductive relations
  Deadline: 12/3/10

  Use the coursework submission (id: 272)) system to submit the coursework
  after demonstrating it in the lab to me or Darin.
  
  Prove the following propositions by
  completing the sheds { .. }.

  Note that not all propositions may be provable. If you think that a
  proposition is unprovable clearly mark this one by adding a line:
  -- impossible.

-}

module ex06 where

open import Data.Nat
open import Relation.Nullary
open import Data.String
open import Relation.Binary.PropositionalEquality

{- Even

  we inductively define the predicate even.

 -}

data Even : ℕ → Set where
  zero : Even zero
  sucsuc : ∀ {n} → Even n → Even (suc (suc n))

{- show that 4 is even. -}

even4 : Even 4
even4 = {!!}

{- show that 3 is not even. -}

¬even3 : ¬ (Even 3)
¬even3 = {!!}

{- show that sucsuc is invertible -}

inv-sucsuc : ∀ {n} → Even (suc (suc n)) → Even n 
inv-sucsuc = {!!}

{- show that there is at most one proof of even. -}

even-unique : ∀ {m} → (p q : Even m) → p ≡ q
even-unique = {!!}

{- show that even is decidable. -}

even? : (n : ℕ) → Dec (Even n)
even? = {!!}

{- Combinatoric logic: we extend propositional logic by conjunction:  -}

data Formula : Set where
  Atom : String → Formula
  _⇒_ : (A B : Formula) → Formula
  _∧_ :  (A B : Formula) → Formula

data Context : Set where
  ε : Context
  _·_ : (Γ : Context) → (A : Formula) → Context

infixl 7 _∧_
infixr 6 _⇒_ 
infix 4 _⊢sk_
infix 4 _⊢_
infixl 5 _·_

data _⊢_ : Context → Formula → Set where
  ass : ∀ {Γ A} → Γ · A ⊢ A
  weak : ∀ {Γ A B} → Γ ⊢ A → Γ · B ⊢ A
  app : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  abs : ∀ {Γ A B} → Γ · A ⊢ B → Γ ⊢ A ⇒ B
  {- To prove a conjuction we prove both components -}
  pair : ∀ {Γ A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ∧ B
  {- To use a conjunction is the same as assuming both components -}
  elim : ∀ {Γ A B C} → Γ · A · B ⊢ C → Γ · A ∧ B ⊢ C

{- In combinatory logic we add three combinators pair, fst and snd -}

data _⊢sk_ : Context → Formula → Set where
  ass : ∀ {Γ A} → Γ · A ⊢sk A
  weak : ∀ {Γ A B} → Γ ⊢sk A → Γ · B ⊢sk A
  app : ∀ {Γ A B} → Γ ⊢sk A ⇒ B → Γ ⊢sk A → Γ ⊢sk B
  K : ∀ {Γ A B} → Γ ⊢sk A ⇒ B ⇒ A
  S : ∀ {Γ A B C} → Γ ⊢sk (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
  pair : ∀ {Γ A B} → Γ ⊢sk A ⇒ B ⇒ A ∧ B
  fst : ∀ {Γ A B} → Γ ⊢sk A ∧ B ⇒ A
  snd : ∀ {Γ A B} → Γ ⊢sk A ∧ B ⇒ B

{- Show that the two derivation relations are equivalent.

  Hint: You are welcome to reuse (and extend) proofs from l11.agda 
-}

⊢sk→⊢ : ∀ {Γ A} → Γ ⊢sk A → Γ ⊢ A
⊢sk→⊢ = {!!}

⊢→⊢sk : ∀ {Γ A} → Γ ⊢ A → Γ ⊢sk A
⊢→⊢sk = {!!}

