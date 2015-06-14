{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Thorsten Altenkirch

  Lecture 9: Arithmetic and fast reverse

  In this lecture we look at proving simple equalities over the
  natural numbers by writing recursive programs. We will then use
  those to implement fast reverse on vectors.
-}
module l09 where

{- We start using the library, but hide the definitions of + and ≤
   because we are going to redefine them. -} 
open import Data.Nat hiding ( _+_ ; _≤_ ) -- natural numbers
open import Data.Vec -- contains the definition of vectors
open import Relation.Binary.PropositionalEquality -- defines ≡ 

{- we define + by recursion over the first argument. -}
_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

{- An alternative would be to define it by recursion over the 2nd -}
_+'_ : ℕ → ℕ → ℕ
m +' zero = m
m +' suc n = suc (m +' n)

{- What is the difference between + and +'?
   The are extensionally equivalent, but they are intensionally
   different. That is they behave different when we program (or prove)
   things about them.
-}

{- Let's prove some basic equations -}

{- It is obvious that zero is left neutral, indeed this 
   follows from the 1st line of the definition of +. Hence the prove
   is also trivial. "By definition" translates to "refl".
-}
0+ : (n : ℕ) → zero + n ≡ n
0+ n = refl

{- While it is true that zero is also right neutral, it is less
   obvious. It doesn't follow from the definition. Indeed, if we try

+0 : (n : ℕ) → n + zero ≡ n
+0 n    = refl

  Agda complaints by saying: n + 0 != n ? This means that n + 0 isn't
  definitionally equal to n. However they are propositionally equal
  (≡), which we can prove using pattern matching and recursion.

-}

+0 : (n : ℕ) → n + zero ≡ n
+0 zero    = refl
+0 (suc n) = cong suc (+0 n)

{- In the suc case we use 
   cong f :  m ≡ n → f m ≡ f n
   which we proved in the previous lecture (but called it resp).
   "cong" stands for congruence. This and other gadgets to reason
   about equality are defined in Relation.Binary.PropositionalEquality -}

{- What changes in the previous proofs, if we use +' instead of + ? -}

{- Let's look at the interaction of + and suc -}

{- suc in the first argument commutes with + and this follows from the
   definition. -}
suc+ : (m n : ℕ) → (suc m) + n ≡ suc (m + n)
suc+ m n = refl

{- suc also commutes with + in the 2nd argument, but as before for +0 
   this requires a recursive proof. -}

+suc : (m n : ℕ) → m + (suc n) ≡ suc (m + n)
+suc zero n = refl
+suc (suc m) n = cong suc (+suc m n)

{- We have now all the pieces together to prove commutativity of addition. 
   Basically we do yet another recursion and in each case exploit the lemmas 
   we have proven previously.
-}

+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm m zero    = +0 m
+-comm m (suc n) = trans (+suc m n) (cong suc (+-comm m n))

{- In the successor case we have to combine +suc and the recursive
   proof of +-comm using transitivity (trans). 
-}

{- What does this "program" actually compute? Let's evaluate
   +-comm 3 7
   using C-c C-n (normalize expression).
   right "refl" because "3 + 7" and "7 + 3" both reduce to 10
   and "refl" proves "10 ≡ 10". However, we can't replace +-comm by 
   
   +-comm m n = refl

   because the typechecker wouldn't accept it.

   Running +-comm doesn't tell us anything new (hence we should
   never execute it) but having it is useful as the following example
   shows. 

   Remember in l02 we tried to define ++' (actually the auxilliary
   function for fast reverse).

_++'_ : {A : Set} → {m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
as ++' [] = as
as ++' (b ∷ bs) = (b ∷ as) ++' bs

  but the type checker wouldn't accept it. In the []-clause it expects
  a "Vec A (m + 0)" but sees "Vec A m" and similarily in the ∷-clause
  it expects "Vec (m + (succ n)" but sees "Vec (suc m) + n". This
  should ring a bell.

  Indeed combining our lemmas above with "subst" we can coerce between
  the instances of Vec with provably equal indizes. Given a family "B
  : A → Set" and "a b : A" which are equal "p : a ≡ b" we can coerce
  
  subst B p : P a → P b

  See last lecture for the proof. We use this to write ++' and reverse
  (rev). 
-}

_++'_ : {A : Set}{m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
_++'_ {A} {m} {zero}  as  [] 
  = subst (Vec A) (sym (+0 m)) as
_++'_ {A} {m} {suc n} as  (b ∷ bs) 
  = subst (Vec A) (sym (+suc m n)) (b ∷ as ++' bs)

{- Note that we had to use the prefix version of ++' to be able to
   access the implicit arguments. -}

{- We can now implement rev easily, and we know from its type that it
   is length preserving.  -}

rev : {A : Set}{m : ℕ} → Vec A m → Vec A m
rev as = [] ++' as

{- Hence "programs" like +0 , +succ and +-comm are useful as witnesses
   at compile time to verify that we performed safe coercions. -}