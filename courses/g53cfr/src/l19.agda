module l19 where

{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Peter Morris

  Lecture 19: Merge Sort (IV)

  As a final trick with our Merge Sort algorithm, we will show that the output
  of the sort function is a _sorted_ list. To do this we must first define what
  it is to be a sorted list. For clarity we shall lose the size indicies, though
  it's straight forward to combine the two proofs and show the output to be
  sorted, and of the right size:

-}

open import Data.List
open import Data.Nat hiding (_≤_ ; _<_)
open import Data.Product

{-

  The first change is that we will now want proofs of the ordering between the 
  numbers we are sorting. So let's bring back the inductive definition of _≤_
  you've used before, and the proof that it is transitive:

-}

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

trans≤ : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
trans≤ z≤n q = z≤n
trans≤ (s≤s m≤n) (s≤s n≤o) = s≤s (trans≤ m≤n n≤o)

{-

  We will also want _<_ and a proof that if m < n the m ≤ n:

-}

_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n

<implies≤ : ∀ {m n} → m < n → m ≤ n
<implies≤ {zero} (s≤s m≤n) = z≤n
<implies≤ {suc m} (s≤s m≤n) = s≤s (<implies≤ m≤n)

{- 

  Now we adapt our order type to talk about the numbers we are sorting,
  Order m n is _either_ a proof that m ≤ n or the n < m:

-} 

data Order : ℕ → ℕ → Set where 
  le : {m n : ℕ} → m ≤ n → Order m n
  gt : {m n : ℕ} → n < m → Order m n

{-

  And our function order must now produce the proof object so, in the recursive
  case we must inspect the recursive call:

-}

order : (m n : ℕ) → Order m n 
order zero n = le z≤n
order (suc m) zero = gt (s≤s z≤n) 
order (suc m) (suc n) with order m n
... | le p = le (s≤s p) 
... | gt q = gt (s≤s q)


{-

  Before we continue we must explain what an order list is, and to do so we must
  index our lists by their lower bound, a natural number which is ≤ all the 
  elements in the list. (For simplicity we have fixed the element type of OList
  to ℕ)

-}

data OListℕ : ℕ → Set where
  {- The empty list is ordered and can have _any_ lower bound -}
  [] : {b : ℕ} → OListℕ b 
  {- To add an element, we must produce a proof that it is not smaller than the 
     lower bound. Note that the head element the serves as the lower bound for 
     the rest of the list: -}
  _-_∷_ : {b : ℕ} → (n : ℕ) → b ≤ n → OListℕ n → OListℕ b

{-

  We can throw away the proofs, to recover a normal list:

-}

fog : {b : ℕ} → OListℕ b → List ℕ
fog [] = []
fog (n - _ ∷ ns) = n ∷ fog ns

{-

  The type of the merge function now expresses the fact that it takes two
  sorted lists and produces a sorted list as a result, note that the result of
  the order function provides the proofs that we need to show that the reult 
  list is in fact sorted:

-}

mutual
 merge : {b : ℕ} → OListℕ b → OListℕ b → OListℕ b
 merge [] ns = ns 
 merge (m - p ∷ ms) [] = m - p ∷ ms
 merge (m - p ∷ ms) (n - q ∷ ns) with order m n 
 ... | le p' = m - p ∷ merge ms (n - p' ∷ ns) 
 ... | gt q' = n - q ∷ merge' m (<implies≤ q') ms ns

 merge' : {b : ℕ} (m : ℕ) → b ≤ m → OListℕ m → OListℕ b → OListℕ b
 merge' m p ms [] = m - p ∷ ms
 merge' m p ms (n - q ∷ ns) with order m n
 ... | le p' = m - p ∷ merge ms (n - p' ∷ ns) 
 ... | gt q' = n - q ∷ merge' m (<implies≤ q') ms ns


{- 

  Recall that the trees we build are not sorted in this algortihm, so the code 
  for this part remains unchanged:

-}

data Parity : Set where p0 p1 : Parity

data DealT (X : Set) : Set where
  empT : DealT X
  leafT : X → DealT X
  nodeT : Parity → DealT X → DealT X → DealT X

insert : {X : Set} → X → DealT X → DealT X
insert x empT = leafT x
insert x (leafT y) = nodeT p0 (leafT y) (leafT x)
insert x (nodeT p0 l r) = nodeT p1 (insert x l) r
insert x (nodeT p1 l r) = nodeT p0 l (insert x r)
 
deal : List ℕ → DealT ℕ
deal [] = empT
deal (n ∷ ns) = insert n (deal ns)

{-

  But now when we merge a tree, or sort a list the result is an ordered list. 
  (Note that we are able to use 0 as the default lower bound only because ℕ has 
  0 as its least element - we could not do this, for instance, if we were 
  sorting integers)

-}

mergeT : DealT ℕ → OListℕ 0
mergeT empT = []
mergeT (leafT n) =  n - z≤n ∷ []
mergeT (nodeT p l r) = merge (mergeT l) (mergeT r)

sort : List ℕ → OListℕ 0
sort ns = mergeT (deal ns)

ex1 : List ℕ 
ex1 = 5 ∷ 2 ∷ 0 ∷ 1 ∷ 4 ∷ 3 ∷ []

ex2 : List ℕ 
ex2 = 100 ∷ 1 ∷ 10 ∷ 1 ∷ 100 ∷ 10 ∷ []


