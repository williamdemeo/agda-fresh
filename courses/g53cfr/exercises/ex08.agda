{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Thorsten Altenkirch

  Exercise 8: Coinductive types
  Deadline: 26/3/10

  Use the coursework submission (id: 284) system to submit the coursework
  after demonstrating it in the lab to me or Darin.
  
  Prove the following propositions by
  completing the sheds { .. }.

  Note that not all propositions may be provable. If you think that a
  proposition is unprovable clearly mark this one by adding a line:
  -- impossible.

-}

module ex08 where

open import Coinduction
--open import Data.Stream
open import Data.Bool
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
--open import Data.Product
open import l15 -- import the lecture from Tuesday
open import Relation.Binary.PropositionalEquality
open import Algebra
module ℕ = CommutativeSemiring Data.Nat.Properties.commutativeSemiring

mutual 

 {- Define operations evens and odds which return
    a stream of all the even and odd elements of the given stream. -}

 evens : ∀ {A} → Stream A → Stream A
 evens = ?

 odds : ∀ {A} → Stream A → Stream A
 odds = ?

{- Define an operation merge which merges two streams like a zipper -}

merge : ∀ {A} → Stream A → Stream A → Stream A 
merge =  ?

{- And prove it correct -}

mergeLem : ∀ {A} → (as : Stream A) → merge (evens as) (odds as) ≈ as
mergeLem = ?

{- Prove the following equality. You will need to use algebraic properties of the natural numbers.
   Also I recommend to prove the following lemma first: 
   evensLem' : (m n : ℕ) → (m ≡ n + n) → evens (from m) ≈ mapStream (λ n → n + n) (from n)
-}

evensLem : (n : ℕ) → evens (from (n + n)) ≈ mapStream (λ n → n + n) (from n)
evensLem = ?

{- We define infinite binary trees: -}
data Tree∞ (A : Set): Set where
  _〈_〉_  : (l : ∞ (Tree∞ A)) → (a : A) → (r : ∞ (Tree∞ A)) → Tree∞ A

infix 4 _≈T_

{- and the notion of extensional equivalence: -}
data _≈T_ {A : Set} : Tree∞ A → Tree∞ A → Set where
  _〈〉_  : ∀ {l l' a r r'} → ∞ (♭ l ≈T ♭ l') 
                       → ∞ (♭ r ≈T ♭ r') 
                       → (l 〈 a 〉 r) ≈T (l' 〈 a 〉 r')

{- Show that ≈T is an equivalence relation. -}
refl≈T : {A : Set} → (t : Tree∞ A) → t ≈T t 
refl≈T = ?

sym≈T : {A : Set}{t u : Tree∞ A} → t ≈T u → u ≈T t 
sym≈T = ?

trans≈T : {A : Set}{t u v : Tree∞ A} → t ≈T u → u ≈T v → t ≈T v 
trans≈T = ?

{- Find a set X so that infinite binary trees are (extensionally) isomorphic to functions over X -}

X : Set
X = List Bool

φ : {A : Set} → Tree∞ A → X → A
φ = ?

ψ :  {A : Set} → (X → A) → Tree∞ A
ψ = ?

{- Show that the two functions defined previously are inverse to each other. -}

ψφ : {A : Set}(t : Tree∞ A) → ψ (φ t) ≈T t
ψφ = ?

φψ : {A : Set}(f : X → A)(bs : X) → φ (ψ f) bs ≡ f bs
φψ = ?
