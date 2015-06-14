{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Thorsten Altenkirch

  Lecture 8: The Axiom of Choice

-}
module l08 where

open import l05 -- we are going to use the definitions for
open import l06 -- we are going to use ¬¬
open import l07 -- we are going to use the definitions for predicate logic

{- Here is a more readable account of the Axiom of Choice.
   Given sets  {A B : Set}
   and a relation {R : A → B → Prp}
   We assume
   ∀ a : A, ∃ b : B, R a b
   and from this we want to conclude
   ⇒ ∃ f : A → B, ∀ a : A, R a (f a)
-}

{- Using our combinators it doesn't look as nice: -}
AC : Set₁
AC = {A B : Set}{R : A → B → Prp} → 
     (∀' A λ a → ∃ B λ b → R a b)
     ⇒ ∃ (A → B) λ f → ∀' A λ a → R a (f a)

{- While this is not provable in classical set theory, it is provable
   in Agda exploiting the Curry-Howard correspondence. 
   The key is to derive the following properties of exist: -}

{- From a proof of an existential statement we can extract 
   a witness: -}
wit : {A : Set}{P : A → Prp} → ∃ A P → A
wit (a , p) = a
{- Note that wit really exploits the identification of Prp and Set. -}

{- And show that the witness satisfies the predicate: -}
prf : {A : Set}{P : A → Prp} → (p : ∃ A P) → P (wit p)
prf (a , p) = p

{- These look very much like ... projections: fst , snd -}

{- Using wit and prf the proof of AC is straight forward: -}
ac : AC
ac h = (λ a → wit (h a)) , λ a → prf (h a)

{- In classical set theory AC is an axiom. The reason is that the
classical axiom corresponds to the following statement (double
negating all existential quantifiers): -}

CAC : Set₁
CAC = {A B : Set}{R : A → B → Prp} → 
     (∀' A λ a → ¬¬ (∃ B λ b → R a b))
     ⇒ ¬¬ (∃ (A → B) λ f → ∀' A λ a → R a (f a))

{- CAC is not provable in Agda. -}