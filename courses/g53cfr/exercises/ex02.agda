{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Thorsten Altenkirch

  Exercise 2: Vector using Vec (5/2/09)
  Deadline: 15/2/09, 12:00

  Use the coursework submission (id: 261) system to submit the coursework
  after demonstrating it in the lab to me or Darin.
  
  Redo the previous exercise (ex01) using vectors instead of lists.
  Additionally implement matrix transposition.

  In some cases it is helpful to implement auxilliary functions.
-}

module ex02 where

open import Data.Nat
open import Data.Vec

Vector : ℕ → Set {- Vec n is an n-dimensional vector -}
Vector m = Vec ℕ m

Matrix : ℕ → ℕ → Set {- Matrix m n is an m x n Matrix -}
Matrix m n = Vec (Vector n) m

{- multiplication with a scalar -}
_*v_ : {n : ℕ} → ℕ → Vector n → Vector n
k *v ms = {!!}

v1 : Vector 3
v1 = 1 ∷ 2 ∷ 3 ∷ []

test1 : Vector 3
test1 = 2 *v v1

{- addition of vectors -}
_+v_ : {n : ℕ} → Vector n → Vector n → Vector n
ms +v ns = {!!}

v2 : Vector 3
v2 = 2 ∷ 3 ∷ 0 ∷ []

test2 : Vector 3
test2 = v1 +v v2

{- multiplication of a vector and a matrix -}
_*vm_ : {m n : ℕ} → Vector m → Matrix m n → Vector n
ms *vm nss = {!!}

id3 : Matrix 3 3
id3 = (1 ∷ 0 ∷ 0 ∷ []) 
    ∷ (0 ∷ 1 ∷ 0 ∷ []) 
    ∷ (0 ∷ 0 ∷ 1 ∷ []) 
    ∷ []

test3 : Vector 3
test3 = v1 *vm id3

{- matrix multiplication -}
_*mm_ : {l m n : ℕ} → Matrix l m → Matrix m n → Matrix l n
mss *mm nss = {!!}

inv3 : Matrix 3 3
inv3 = (0 ∷ 0 ∷ 1 ∷ []) 
     ∷ (0 ∷ 1 ∷ 0 ∷ []) 
     ∷ (1 ∷ 0 ∷ 0 ∷ []) 
     ∷ []

test4 : Matrix 3 3
test4 = inv3 *mm inv3

{- implement matrix transposition, i.e. swap rows and columns. -}

transpose : {m n : ℕ} → Matrix m n → Matrix n m
transpose mss = {!!}

rect : Matrix 2 3
rect = (1 ∷ 2 ∷ 3 ∷ [])
     ∷ (4 ∷ 5 ∷ 6 ∷ [])
     ∷ []

test5 : Matrix 3 2
test5 = transpose rect