{-#  OPTIONS --type-in-type #-}
{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Thorsten Altenkirch

  Lecture 20: Russell's paradox

  In this lecture we show that it is inconsistent to have
  Set:Set. Luckily, Agda is aware of this and indeed 
  Set=Set₀ : Set₁ : Set₂ : ...
  (this is called a predicative hierarchy).
  But with the pragma on top if this file, Agda will accept that
  Set:Set which makes it possible to derive Russell's paradox.
-}
module l20 where

open import Data.Nat
open import Data.Bool
open import Data.Unit
open import Data.Product
open import Data.Empty
open import Relation.Binary.PropositionalEquality

{- Russell's paradox: If there is a set of all sets then we can also
   construct the set R of all sets which do not contain themselves

   R = { X : Set | X ∉ X }

   Now if R∈R then R∉R and vice versa, which is inconsistent.

   However, we cannot replace ∈ by : because : is not a predicate (but
   it is a judgement. So to be able to encode Russell's paradox we
   first have to define sets in the sense of Set Theory which have a 
   predicate ∈. We do this by defining a type of trees we call M (for
   Menge = Set in german).
-}

data M : Set where
  m : (I : Set) → (I → M) → M

{- Note that the definition of M already exploits Set : Set, because
   the constructor m has an argument I which is "too large".
-}

{- We can define some basic sets. Note that I use [..] for the names
   of sets because {..} are reserved symbols. -}

-- the empty set
∅ : M
∅ = m ⊥ ⊥-elim

-- the set containing the empty set
[∅] : M
[∅] = m ⊤ (λ _ → ∅)

-- the set containing the empty set and the set containing the empty set
[∅,[∅]] : M
[∅,[∅]] = m Bool (λ x → if x then ∅ else [∅])

{- We can now define ∈ (and ∉ as a predicates: -}
_∈_ : M → M → Set
a ∈ m I f = Σ I (λ i → a ≡ f i)

_∉_ : M → M → Set
a ∉ b = (a ∈ b) → ⊥

{- and define the set R: -}
R : M
R = m (Σ M (λ a → a ∉ a)) proj₁

{- Indeed, every set which is in R does not contain itself -}
lem-1 : ∀ {X} → X ∈ R → X ∉ X
lem-1 ((Y , Y∉Y) , refl) = Y∉Y

{- And every set which does not contain intself is in R -}
lem-2 : ∀ {X} →  X ∉ X → X ∈ R
lem-2 {X} X∉X = (X , X∉X) , refl

{- Now lem-1 already shows that R does not contain itself -}
lem-3 : R ∉ R
lem-3 R∈R = lem-1 R∈R R∈R

{- and from this we can derive a contradiction -}
contr : ⊥
contr = lem-3 (lem-2 lem-3)

{- What happens if we try to evaluate contr. ? -}