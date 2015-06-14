{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Peter Morris

  Lecture 18: Merge Sort (III)

  In the last lecture, we showed that our Merge Sort implementation was 
  terminating. Now we will try to show that sorting preserves the size of the 
  input list. We do this by adapting the implementation to use Vectors, rather 
  than plain Lists. By doing so we can also ensure that the Tree we build
  is balanced, and therefore our algorithm has the right time complexity.

-}

module l18 where

open import Algebra
open import Data.Vec
open import Data.Nat
open import Data.Nat.Properties
private
  module ℕ = CommutativeSemiring commutativeSemiring
open import Data.Product
open import Relation.Binary.PropositionalEquality
import Algebra.RingSolver.AlmostCommutativeRing as ACR
import Algebra.RingSolver.Simple as Solver

open Solver (ACR.fromCommutativeSemiring commutativeSemiring)

zeroLem : (n : ℕ) → n ≡ n + 0
zeroLem = solve 1 (\n → n := n :+ con 0) refl 

sucLem₁ : (m n : ℕ) → (1 + (m + n)) ≡ (m + (1 + n))
sucLem₁ = solve 2 (\m n → con 1 :+ (m :+ n) := m :+ (con 1 :+ n)) refl

sucLem₂ : (m n : ℕ) → (m + (1 + n)) ≡ (1 + (m + n)) 
sucLem₂ m n = sym (sucLem₁ m n)   

{-

  Ordering things doesn't talk about size, so this code stays the same:

-}

data Order : Set where le gt : Order

order : ℕ → ℕ → Order
order zero n = le
order (suc m) zero = gt
order (suc m) (suc n) = order m n

{-

  However, merge, does talk about size, here we must ensure that if we merge
  two vectors, then the result as as many elements as both lists added together:

-}

mutual
 merge : {m n : ℕ} → Vec ℕ m → Vec ℕ n  → Vec ℕ (m + n) 
 merge [] ns = ns 
{-
  In the first base case (above), everything works, in the second (below)
  though, we have to fixe up the types since ms has type Vec ℕ lm and the in 
  hole we need something of type Vec ℕ (lm + 0), so we use subst to coerce
  between these types
-}
 merge {suc lm} {zero} (m ∷ ms) [] = m ∷ subst (Vec ℕ) (zeroLem lm) ms 
 merge {suc lm} {suc ln} (m ∷ ms) (n ∷ ns) with order m n 
 ... | le = m ∷ merge ms (n ∷ ns) 
{-
  Again, in the 2nd recursive case, we must appeal to subst to fix up the types 
  when the definition of + does not provide the equality we need
-}
 ... | gt = n ∷ subst (Vec ℕ) (sucLem₁ lm ln) (merge' m ms ns)  

{- 

  merge' incorporates the same tweaks as merge:

-}

 merge' : {m n : ℕ} → ℕ → Vec ℕ m → Vec ℕ n → Vec ℕ (1 + (m + n))
 merge' {lm} {zero} m ms [] = m ∷ subst (Vec ℕ) (zeroLem lm) ms 
 merge' {lm} {suc ln} m ms (n ∷ ns) with order m n
 ... | le = m ∷ merge ms (n ∷ ns) 
 ... | gt = n ∷ subst (Vec ℕ) (sucLem₁ lm ln) (merge' m ms ns)  

{- 

  We now must adapt our DealT type to take account of size, first of all we'll
  need to embed our Parity type in the the Natural Numbers:

-}

data Parity : Set where p0 p1 : Parity

pℕ : Parity → ℕ
pℕ p0 = 0
pℕ p1 = 1

{-

  Now we can index our trees by their size, empT and leafT have obvious sizes:

-}

data DealT (X : Set) : ℕ → Set where
  empT : DealT X 0
  leafT : X → DealT X 1
{-

  But what about nodeT? We want the two sub trees to have approximately the same
  size. We use the parity bit (and it's embedding in the natural numbers) to
  describe the difference in size between those two trees:

-}
  nodeT : {n : ℕ} (p : Parity) → DealT X (pℕ p + n) → DealT X n 
                               → DealT X (((pℕ p + n) + n))


{- 

  Inserting into a DealT increases its size by 1, note that if we insert into 
  an unbalanced tree (to obtain a balanced one, we must again use subst to fix 
  up the types DealT ℕ (1 + (1 + n) + n) and DealT ℕ (0 + (1 + n) + (1 + n))

-}

insert : {X : Set}{n : ℕ} → X → DealT X n → DealT X (1 + n)
insert x empT = leafT x
insert x (leafT y) = nodeT p0 (leafT y) (leafT x)
insert x (nodeT p0 l r) = nodeT p1 (insert x l) r
insert {X} x (nodeT {n} p1 l r) = subst (\n → DealT X n) (cong suc (sucLem₂ n n)) (nodeT p0 l (insert x r))

{-

  The rest of the code however, does through with out a hitch when we adapt the 
  types to use Vectors:

-}
 
deal : {n : ℕ} → Vec ℕ n → DealT ℕ n
deal [] = empT
deal (n ∷ ns) = insert n (deal ns)

mergeT : {n : ℕ} → DealT ℕ n → Vec ℕ n
mergeT empT = []
mergeT (leafT n) = [ n ]
mergeT (nodeT p l r) = merge (mergeT l) (mergeT r)

sort : {n : ℕ} → Vec ℕ n → Vec ℕ n
sort ns = mergeT (deal ns)

ex1 : Vec ℕ 6 
ex1 = 5 ∷ 2 ∷ 0 ∷ 1 ∷ 4 ∷ 3 ∷ []

ex2 : Vec ℕ 6
ex2 = 100 ∷ 1 ∷ 10 ∷ 1 ∷ 100 ∷ 10 ∷ []