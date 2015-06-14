{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Peter Morris

  Coursework 9: Quick Sort (II)

  You job is to redefine quicksort in an obviously terminating way
  again the key observation to make is that we should rather build concrete
  trees, than complex recursive calls. 

  Complete all missing definitions, and follow all instructions in comments!!!
-}



module ex09ii where

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
  As opposed to Merge Sort, the building of the tree is intertwined with 
  sorting.

  We'll need to store the pivot at each level, and put things less or equal than
  it in the left, and things greater than it in the right sub tree. Thus QS 
  trees must have data in the nodes, rather than the leaves:
-}

data Tree (X : Set) : Set where
  leaf : Tree X
  node : Tree X → X → Tree X → Tree X 

{- 
  The key operation is no 'insert' which puts a natural number its right 
  place in an already sorted tree:
-}

insert : ℕ → Tree ℕ → Tree ℕ
insert n t = {!!}

{-
  We build sorted a sorted list by inserting the elems one at a time:
-}

insertAll : List ℕ → Tree ℕ
insertAll [] = leaf
insertAll (n ∷ ns) = insert n (insertAll ns)

{-
  Once we've built a sorted tree, all that now remains is to flatten it back 
  into a list:
-}

flatten : {X : Set} → Tree X → List X
flatten t = {!!}

{-
  We can sort by building the tree and then flattening it
  
  Convince yoursefl that this algorithm is equivalent to QS and make sure your 
  definition works on some examples:
-}

sort : List ℕ → List ℕ
sort ns = flatten (insertAll ns) 

{-
  !!! IMPORTANT FINAL EXERCISE: !!!

  Show that that sort gives back a list of the same length as the input,
  by adapting it to work on Vectors. You will need to index your tree type
  by a size as well.

  (nb. there is no balancing with these Trees, so you do not need Partity)

  Please submit 2 files, one with length, and one without.
-}

ex1 : List ℕ  
ex1 = 5 ∷ 2 ∷ 0 ∷ 1 ∷ 4 ∷ 3 ∷ []

ex2 : List ℕ
ex2 = 100 ∷ 1 ∷ 10 ∷ 1 ∷ 100 ∷ 10 ∷ []

