{-# OPTIONS --no-termination-check 
  #-}
{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Peter Morris

  Lecture 17: Merge Sort (I)

  We started 3 lectures on implementing, and incrementally refining an 
  implementation of Merge Sort. Our aim is to establish the correctness of
  the implementation, using techniques from earlier lectures:

-}

module l17i where

open import Data.List
open import Data.Nat
open import Data.Product

{- 
  We will only consider sorting lists of natural numbers, for simplicity. 

  We begin by defining a comparison function of two Natural Numbers, this 
  returns an Order (a copy of the Booleans):
-}

data Order : Set where le gt : Order

order : ℕ → ℕ → Order
order zero n = le
order (suc m) zero = gt
order (suc m) (suc n) = order m n

{-
  Now we can explain how to merge two sorted lists of Natural Numbers, using 
  the comparison function above. Remember that naively we wanted to write merge:

merge : List ℕ → List ℕ → List ℕ
merge [] ns = ns
merge (m ∷ ms) [] = m ∷ ms
merge (m ∷ ms) (n ∷ ns) with order m n
... | le = m ∷ merge ms (n ∷ ns)
... | gt = n ∷ merge (m ∷ ms) ns

  But this doesn't pass Agda's termination checker, it analyses the definition 
  to see any inductive argument gets smaller in all recursive calls, which is 
  not the case.

  Instead we must tease this one function out into to mutually defined 
  functions, one we call when ms gets smaller, the other when ms gets smaller:
-} 

mutual
  merge : List ℕ → List ℕ → List ℕ  
  merge [] ns = ns
  merge (m ∷ ms) [] = m ∷ ms
  merge (m ∷ ms) (n ∷ ns) with order m n 
  ...                     | le = m ∷ merge ms (n ∷ ns) 
  ...                     | gt = n ∷ merge' m ms ns

  merge'  : ℕ → List ℕ → List ℕ → List ℕ
  merge' m ms [] = m ∷ ms
  merge' m ms (n ∷ ns) with order m n 
  ...                     | le = m ∷ merge ms (n ∷ ns) 
  ...                     | gt = n ∷ merge' m ms ns


{-
  To sort efficiently, merge sort must split the list to be sorted into 2 lists
  of roughly the same size, to do this we 'deal' the input list out, as if it 
  were a pack of cards:
-}

deal : List ℕ → (List ℕ × List ℕ)
deal [] = [] , []
deal (n ∷ []) = [ n ] , [] 
deal (n ∷ n' ∷ ns) with deal ns
...                | (xs , ys) = n ∷ xs , n' ∷ ys

{-
  And now we can sort, by merging the result of sorting the two 'piles':
-}

sort : List ℕ → List ℕ
sort ns with deal ns 
...     | (xs , []) = xs 
...     | (xs , ys) = merge (sort xs) (sort ys)

{-
  However, Agda is again unconvinced that this terminates, it's is unable to
  see that in the 2 recursive calls that xs and ys are infact smaller than
  the input, ns.
-}


ex1 : List ℕ 
ex1 = 5 ∷ 2 ∷ 0 ∷ 1 ∷ 4 ∷ 3 ∷ []

ex2 : List ℕ 
ex2 = 100 ∷ 1 ∷ 10 ∷ 1 ∷ 100 ∷ 10 ∷ []

