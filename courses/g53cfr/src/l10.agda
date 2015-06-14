{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Thorsten Altenkirch

  Lecture 10: Equality, induction and recursion and decidability.

  We start to look at equality again, compare induction and recursion
  and finally show that equality is "decidable".

-}
module l10 where

{- We start using the library, but hide the definitions of + and ≤
   because we are going to redefine them. -} 

open import Data.Nat hiding ( _+_ ; _≤_ ) -- natural numbers
open import Data.Vec -- contains the definition of vectors
open import Relation.Binary.PropositionalEquality -- defines ≡ 
open import l09 hiding (+-comm ; _+'_) -- last lecture

{- proof irrelevance: 

  There is no information in an equality proof and we can even proof
  this in Agda. We establish the principle of "Uniqueness of Identity
  Proofs" (uip) showing that any two equality proofs are equal.

 -}

uip : {A : Set}{a b : A} (p q : a ≡ b) → p ≡ q
uip refl refl = refl

{- How to beautify your equality proofs.

   Last lecture we proved +-comm using transitivity. How ever using
   the basic combinators for equality is hardly readable.
-}

+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm m zero    = +0 m
+-comm m (suc n) = trans (+suc m n) (cong suc (+-comm m n))

{-
  Luckily, the Agda standard library provides some definitions which
  allow us to present equality derivation in the style of mathematical
  text books.
-}

open ≡-Reasoning
open import Data.Product

+-comm' : (m n : ℕ) → m + n ≡ n + m
+-comm' m zero = +0 m 
+-comm' m (suc n) = begin 
            m + suc n   ≡⟨ +suc m n ⟩
            suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩
            suc n + m  ∎

{- 
  We relate primitive recursion and induction.

  First we define a combinator for primitive recursion: rec.
-}

rec : (A : Set) → A → (ℕ → A → A) → ℕ → A
rec A z s zero = z
rec A z s (suc n) = s n (rec A z s n)

{-
  rec is universal for primitive recursion - all structural recursive
  definitions can be derived using it. As an example we define
  addition. 
-}

_+'_ : ℕ → ℕ → ℕ
_+'_ = rec (ℕ → ℕ) (λ n → n) (λ m m+ n → suc (m+ n))

{- Note that we use the η-law (λ x → f x = f) to omit the parameters. -}

{-
  Using combinators doesn't improve readability.

  We derive the induction scheme:
-}

ind : (P : ℕ → Set) → 
      P zero → 
      ((n : ℕ) → P n → P (suc n)) → 
      (n : ℕ) → P n
ind P z s zero = z
ind P z s (suc n) = s n (ind P z s n)

{-
  The similarity of ind and rec are obvious. Indeed using
  Curry-Howard, induction just is dependent recursion. 

  Let's put "ind" to action, derving the proof of +0:
-}

+0' : (n : ℕ) → n + zero ≡ n
+0' = ind (λ n' → n' + zero ≡ n') refl (λ n +0n → cong suc +0n) 


{- Next we look at "Decidability". 

  Equality on natural numbers is decidable, i.e. we can implement a
  boolean function which retruns true if two numbers are equal, and
  false otherwise.
-}

open import Data.Bool 

_≡b_ : ℕ → ℕ → Bool
zero ≡b zero = true
zero ≡b suc n = false
suc n ≡b zero = false
suc n ≡b suc m = n ≡b m

-- 3 ≡b 3
-- 3 ≡b 4

{- eqb seems to do the job. How can we be sure? We could verify it (as
   we have done in G52MC2. But here we look at an alternative: derive
   a proof/program whose type shows what it does.
-}

open import Relation.Nullary hiding (Dec)

{- We say that a set P is decided if we can either show that it is
   inhabited or that it is not inhabited. I.e. the principle of the
   excluded middle (P ∨ ¬ P) is inhabited.
-}

data Dec (P : Set) : Set where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

{- We prove that ≡ is "decidable", i.e. for every m,n : ℕ we can 
   decide m ≡ n.
-}

_≡?_ : (m n : ℕ) → Dec (m ≡ n)
zero ≡? zero = yes refl
zero ≡? suc n = no (λ ()) -- use the "impossible pattern" in a λ-abstraction.
suc n ≡? zero = no (λ ())
suc n ≡? suc m with n ≡? m
suc n ≡? suc m | yes p = yes (cong suc p)
suc n ≡? suc m | no ¬p = no (λ sn≡sm → ¬p (cong pred sn≡sm))

-- 3 ≡? 3
-- 3 ≡? 4

{- The similarity with ≡b should be obvious. The difference is that ≡?
   doesn't just say "yes" or "no" corresponding to "true" and "false"
   but it also provides the evidence why it is ok to give this answer.

   Also we should note that ≡? is at the same time a program and a proof. 
-}