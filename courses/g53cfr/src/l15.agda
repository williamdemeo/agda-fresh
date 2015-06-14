{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Thorsten Altenkirch

  Lecture 15: Coinductive definitions

  In this lecture we look at infinite structures, in particular
  streams which are infinite sequences (similar to lists which are
  finite sequences). We are using Agdas type of delayed computations
  (∞ A) to represent infinite structures. Applying the Curry-Howard
  isomorphism we can also represent infinite proofs. We are using this
  to define bisimilarity, i.e. extensional equality of streams.

-}
module l15 where

open import Coinduction
open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality

{-
Agda doesn't permit the construction of infinite lists (as in Haskell)
because lists are defined inductively, hence all lists must be
constructable with a finite amount of constructors.

As a consequence Agda rejects the following program:

from : ℕ → List ℕ
from n = n ∷ from (suc n)
-}

{- To represent infinite sequences we define the type of streams using 
   ∞ X which represents "delayed computations of X". Because we are
   not constructing the whole stream now we can represent an infinite
   objects. This is reminiscent of the definition of a function - we
   don't calculate its values yet but only when required. -}

infix 5 _∷_

data Stream (A : Set) : Set where
  _∷_ : A → ∞ (Stream A) → Stream A

{- ∞ comes with two basic operations

♯ : A → ∞ A (delay, turn a term into a delayed computation)
♭ : ∞ A → A (forcing a delayed computation to evaluate)

∞ = \infty, ♯ = \sharp, ♭ = \flat
-}


{- We can now define ℕ by delaying the recursive computation of the
   tail of the stream.-}
from : ℕ → Stream ℕ
from n = n ∷ ♯ (from (suc n))

{- We can access the tails of the stream using: -}
tail : ∀ {A} → Stream A → Stream A
tail (a ∷ as) = ♭ as

{- Or more generally we can obtain a list of the first n elements of a
   stream. -}
taken : ∀ {A} → Stream A → ℕ → List A
taken (a ∷ as) zero = []
taken (a ∷ as) (suc n) = a ∷ taken (♭ as) n

{- Try "taken (from 0) 10" -}

{- It is important that a recursive definition computing a stream
   (such as from) is "productive", i.e. whenever we want to access any
   component of the stream we can do this by forcing previously
   delayed computation. -}

{- The following is an example of a non-productive definition which is
   rejected by Agda

bad : Stream ℕ
bad = 0 ∷ (♯ (tail bad))

   While we can compute the head of bad (0) we cannot calculate its tail,
   because it is just defined by itself (bad recursion). 

   Agda recognizes productive definitions, if they are "guarded". I.e. ♯
   guards a recursive call and there are only constructors in between
   ♯ and the recursive call, not arbitrary functions like tail.

   Note that there are cases of productive definitions which are not
   guarded. Agda will reject them and we have to find another way to
   calculate the result. This is similar to recursive definitions
   which are structurally recursive but this is not always recognized
   by Agda.
-}

{- Let's prove a simple theorem about "from".

   First of all we notice that Stream like List is a "functor", i.e. 
   we can "map" a function over a stream:
-}
mapStream : {A B : Set} → (A → B) → Stream A → Stream B
mapStream f (a ∷ as) = f a ∷ ♯ (mapStream f (♭ as))
{- 
    "mapStream f as" applies the function f to each of the components
   of as. Note that the definition of mapStream is guarded and that
   each time we force the output (i.e. force the delayed computation 
   "♯ (mapStream f (♭ as)") this will in turn force further
   computation of the input by evaluating "♭ as".
-}
{-
  The theorem we want to prove is that mapping suc to from n is the
   "same" as from (suc n):

  (n : ℕ) → mapStream suc (from n) ≡ from (suc n)

  However, we are unable to prove the theorem in the above form. The
  reason is that Agdas propositional equality (≡) is too
  "intensional". Consider

  "mapStream suc (from zero)"
  this evaluates to something like
  "1 ∷ .l15.♯-2 suc 0 (.l15.♯-0 0)"

  "from (suc zero)"
  this evaluates to something like
  "1 ∷ .l15.♯-0 1"

  While the heads of the streams (1) are clearly definitionally equal
  the tails are different delayed computation. Moreover both
  expressions are closed and hence the only way to prove 

  "mapStream suc (from zero) ≡ from (suc zero)"

  would be by refl but this is only possible if they are
  definitionally equal. 

  Hence we need a different "extensional" equality for streams. 
  This equality should identify two streams which have identical
  components.

  The main idea for the definition is to apply the idea of a delayed
  computation into the delayed computation of a stream. Hence we
  define:
  
-}
infix 4 _~_

data _~_ {A} : (xs ys : Stream A) → Set where
  _∷_ : ∀ {x y xs ys} → (x ≡ y) → ∞ (♭ xs ~ ♭ ys) → x ∷ xs ~ y ∷ ys

{- The idea is that to prove that two streams are equal we show that
   the heads are equal and provide a delayed computation proving that
   the tails are equal. -}

infix 4 _≈_
{-
  The definition used in the Agda library gets rid of the equality
  proofs by noting that we can just identitfy x and y. It is easy to
  show that both are equivalent.
-}

data _≈_ {A} : (xs ys : Stream A) → Set where
  _∷_ : ∀ x {xs ys} (xs≈ : ∞ (♭ xs ≈ ♭ ys)) → x ∷ xs ≈ x ∷ ys

{- For historic reasons the relation _≈_ is called "bisimularity"
   because it is conventionally defined via "bisimulation". Our
   definition using Curry-Howard and the idea of a delayed computation
   is an alternative.
-}

{- It is now surprisingly easy to prove the reformulated nthLem: -}

nthLem : (n : ℕ) → mapStream suc (from n) ≈ from (suc n)
nthLem n = suc n ∷ ♯ nthLem (suc n)

{- We simply observe that the heads of both sides are identical and
   that the tails are an instance of the theorem we are just about to
   prove. Hence we can construct an infinite proof that both streams
   are equal. 
-}

{- We show that ≈ is an equivalence relation using infinite proofs
   again.  -}

refl≈ : ∀ {A} → (as : Stream A) → as ≈ as
refl≈ (a ∷ as) = a ∷ ♯ (refl≈ (♭ as))

sym≈ : ∀ {A} → {as bs : Stream A} → as ≈ bs → bs ≈ as
sym≈ (a ∷ as≈bs) = a ∷ ♯ sym≈ (♭ as≈bs)

trans≈ : ∀ {A} → {as bs cs : Stream A} → as ≈ bs → bs ≈ cs → as ≈ cs
trans≈ (a ∷ as≈bs) (.a ∷ bs≈cs) = a ∷ ♯ (trans≈ (♭ as≈bs) (♭ bs≈cs))

