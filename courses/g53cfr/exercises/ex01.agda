{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Thorsten Altenkirch

  Exercise 1: Vector using lists (28/1/09)
  Deadline: 5/2/09, 12:00

  Use the coursework submission (id: 258) system to submit the coursework
  after demonstrating it in the lab to me or Darin.
  
  In this exercise we implement operations on vectors and matrices
  (over ℕ) using lists in Agda. We will learn some better
  representation next week...

  Complete all the sheds! {! .. !}

-}

module ex01 where

open import Data.Nat
open import Data.List

Vector : Set 
Vector = List ℕ -- a vector is a list of natural numbers

Matrix : Set
Matrix = List Vector -- a matrix is a list of vectors

{- we can mulitply a number with a vector,
   x *v [a1 .. an] = [x*a1 .. x*an] -}
_*v_ : ℕ → Vector → Vector
k *v xs = {!!}

v1 : Vector
v1 = 1 ∷ 2 ∷ 3 ∷ []

test1 : Vector
test1 = 2 *v v1

{- we can add vectors componentwise
   [a1 .. 1n] +v [b1 .. bn] = [a1+b1 .. an+bn]
   if one vector is shorter the missing entries are interpreted as 0.
-}
_+v_ : Vector → Vector → Vector
xs +v ys = {!!}

v2 : Vector
v2 = 2 ∷ 3 ∷ []

test2 : Vector
test2 = v1 +v v2

{- we can multiply a vector with a matrix
   [ a1         [ [b11 .. b1m]
     ..    *vm        ..
     an ]         [bn1 .. bnm ]

             =  [ a1*b11+..+an*bn1 .. a1*b1m+..+an*bnm]

   again if entries are missing they are interpreted as 0.
-}

_*vm_ : Vector → Matrix → Vector
xs *vm yss = {!!}

{- hint use the +v , *vm -}

id3 : Matrix
id3 = (1 ∷ []) 
    ∷ (0 ∷ 1 ∷ []) 
    ∷ (0 ∷ 0 ∷ 1 ∷ []) 
    ∷ []

test3 : Vector
test3 = v1 *vm id3

{- we can also multiply matrices with matrices
   [ [ a11  .. [al1          [ [b11 .. b1m]
         ..     ..     *mm         ..
       a1n] .. aln] ]          [bn1 .. bnm ] ]

             =  [ a11*b11+..+a1n*bn1 .. a11*b1m+..+a1n*bnm
                                  ..
                  al1*b11+..+anl*bn1 .. al1*bnm+..+aln*bnm ]
-}

_*mm_ : Matrix → Matrix → Matrix
xss *mm yss = {!!}

{- hint: use *vm -}

inv3 : Matrix
inv3 = (0 ∷ 0 ∷ 1 ∷ []) 
     ∷ (0 ∷ 1 ∷ []) 
     ∷ (1 ∷ []) 
     ∷ []

test4 : Matrix
test4 = inv3 *mm inv3
