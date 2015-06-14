{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Peter Morris

  Coursework 9: Quick Sort

  In this coursework, we're going to look at another sorting algorithm
  Quick Sort. The naive implementation is below:
-}



module ex09i where

open import Data.List
open import Data.Nat
open import Data.Product

{-
  Order and order are as before:
-}

data Order : Set where le gt : Order

order : ℕ → ℕ → Order
order zero n = le
order (suc m) zero = gt
order (suc m) (suc n) = order m n

{-
  The key with QS is to split a list in to two parts, one part with numbers
  less or equal than some given pivot, and the second list with numbers greater
  than the pivot:
-}

pivot : ℕ → List ℕ → (List ℕ × List ℕ)
pivot n [] = [] , []
pivot n (m ∷ ms) with pivot n ms | order m n
... | xs , ys | le = m ∷ xs , ys
... | xs , ys | gt = xs , m ∷ ys

{- 
  Sorting then involves picking a pivot from the front of the list, spliting 
  the rest of the list, sorting the two parts and putting everything back 
  together (note, that the pivot has to go in the _middle_ now:
-}


sort : List ℕ → List ℕ
sort [] = []
sort (n ∷ ns) with pivot n ns
... | (xs , ys) = sort xs ++ (n ∷ sort ys)

{-
  Sadly, again, this isn't obviously terminating (at least to Agda). So your job
  is to redefine QS in a structurally recursive way, in QuickSort2.agda
-} 


ex1 : List ℕ  
ex1 = 5 ∷ 2 ∷ 0 ∷ 1 ∷ 4 ∷ 3 ∷ []

ex2 : List ℕ
ex2 = 100 ∷ 1 ∷ 10 ∷ 1 ∷ 100 ∷ 10 ∷ []

