{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Thorsten Altenkirch

  Exercise 7: Evaluation and compilation
  Deadline: 19/3/10

  Use the coursework submission (id: ???) system to submit the coursework
  after demonstrating it in the lab to me or Darin.
  
  Prove the following propositions by
  completing the sheds { .. }.

  Note that not all propositions may be provable. If you think that a
  proposition is unprovable clearly mark this one by adding a line:
  -- impossible.

-}

module ex07 where

{- This week's exercise is to extend the typed evaluator and compiler
   we have looked at this week by adding products to it.
-}

open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Data.Product hiding (_×_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

{- an untyped language of expressions -}

infix 3 _≤E_
infix 4 _+E_
infix 4 _,_

{- We extend Expr by operations for products -}
data Expr : Set where
  nat : ℕ → Expr
  bool : Bool → Expr
  _+E_ : Expr → Expr → Expr
  _≤E_ : Expr → Expr → Expr
  ifE_then_else_ : Expr → Expr → Expr → Expr
  _,_ : Expr → Expr → Expr
  fst : Expr → Expr
  snd : Expr → Expr

{- Examples of expressions: -}

e1 : Expr 
e1 = fst (nat 3 , nat 4) +E nat 7

e2 : Expr -- 3 ≤ 4 + 5
e2 = ifE fst (fst (bool true , nat 3) , nat 4) then nat 0 else nat 1

e3 : Expr -- (3 ≤ 4) + 5
e3 = ifE snd (fst (bool true , nat 3) , nat 4) then nat 0 else nat 1

{- The result of evaluating an expression is a value -}

data Val : Set where
  nat : ℕ → Val
  bool : Bool → Val
  _,_ : Val → Val → Val 

{- implement the evaluator for this language
   extending the one from the lecture
-}

⟦_⟧ : Expr → Maybe Val
⟦ e ⟧ = {!!}

{- Evaluation the examples: -}

v1 : Maybe Val -- just (nat 10)
v1 = ⟦ e1 ⟧

v2 : Maybe Val -- just (nat 0)
v2 = ⟦ e2 ⟧

v3 : Maybe Val
v3 = ⟦ e3 ⟧ -- nothing

{- We do everything again but this time for a typed language. -}

infix 6 _×_

{- the types -}
data Ty : Set where
  nat : Ty
  bool : Ty
  _×_ : Ty → Ty → Ty

{- typed values -}
data TVal : Ty → Set where
  nat : ℕ → TVal nat
  bool : Bool → TVal bool
  _,_ : ∀ {σ τ} → TVal σ → TVal τ → TVal (σ × τ)

{- Extend the type of typed expressions : -}

data TExpr : Ty → Set where
  nat : ℕ → TExpr nat
  bool : Bool → TExpr bool
  _+E_ : TExpr nat → TExpr nat → TExpr nat
  _≤E_ : TExpr nat → TExpr nat → TExpr bool
  ifE_then_else_ : {σ : Ty} → TExpr bool → TExpr σ → TExpr σ → TExpr σ
  -- add extra constructors

{- Extend the typed evaluator. -}
⟦_⟧T : {σ : Ty} → TExpr σ → TVal σ
⟦ _ ⟧T = {!!}

{- A forgetful map from typed expressions to untyped expressions -}
⌊_⌋ : {σ : Ty} → TExpr σ → Expr
⌊ e ⌋ = {!!}

infix 0 _≡Ty?_

{- Show that the extended notion of types is still decidable.
   This may require some lemmas.
-}
_≡Ty?_ : (σ τ : Ty) → Dec (σ ≡ τ)
σ ≡Ty? σ' = {!!}

{- The result of checking an expression e is a record containing: -}
record Check (e : Expr) : Set where
  constructor check
  field 
    σ : Ty                -- a type
    te : TExpr σ          -- a typed expression
    te≡e : ⌊ te ⌋ ≡ e    -- if we forget the types we recover e

open Check

{- extend the type inference algorithm -}
infer : (e : Expr) → Maybe (Check e)
infer e = {!!}

{- A safe evaluator -}

{- We can also forget the types of typed values -}
⌊_⌋v : {σ : Ty} → TVal σ → Val
⌊ v ⌋v = {!!}

⟦_⟧s : Expr → Maybe Val
⟦ e ⟧s = {!!}

{- For our examples that safe evaluator produces the same results: -}

v1' : Maybe Val
v1' = ⟦ e1 ⟧s

v2' : Maybe Val
v2' = ⟦ e2 ⟧s

v3' : Maybe Val
v3' = ⟦ e3 ⟧s

{- Is this always the case ? -}

{- We extend the untyped assembly code -}

data Code : Set where
  push : Val → Code → Code
  +M : Code → Code
  ≤M : Code → Code
  branch : Code → Code → Code
  stop : Code
  -- add extra constructors

data Stack : Set where
  ε : Stack
  _▹_ : Stack → Val → Stack

run : Stack → Code → Maybe Stack
run s p = {!!}

compile : Expr → Code → Code
compile e p = {!!}

compileRun : Expr → Maybe Val
compileRun e = {!!}

v1'' : Maybe Val
v1'' = compileRun e1

v2'' : Maybe Val
v2'' = compileRun e2

v3'' : Maybe Val
v3'' = compileRun e3

--- Extend the typed assembly language
infixl 4 _▹_

data StackTy : Set where
    ε : StackTy
    _▹_ : StackTy → Ty → StackTy

data TStack : StackTy → Set where
  ε : TStack ε
  _▹_ : ∀ {Γ σ} → TStack Γ → TVal σ → TStack (Γ ▹ σ)
    
data TCode : StackTy → StackTy → Set where
  push : ∀ {Γ Δ σ} → TVal σ → TCode (Δ ▹ σ)  Γ → TCode Δ Γ
  +M : ∀ {Γ Δ} → TCode (Δ ▹ nat) Γ → TCode (Δ ▹ nat ▹ nat) Γ
  ≤M : ∀ {Γ Δ} → TCode (Δ ▹ bool) Γ → TCode (Δ ▹ nat ▹ nat) Γ
  branch : ∀ {Γ Δ} → TCode Δ Γ → TCode Δ Γ → TCode (Δ ▹ bool) Γ
  stop : ∀ {Γ} → TCode Γ Γ
  -- add extra constructors

trun : ∀ {Γ Δ} → TStack Γ → TCode Γ Δ → TStack Δ
trun s p = {!!}

tcompile : ∀ {Γ Δ σ} → TExpr σ → TCode (Γ ▹ σ) Δ → TCode Γ Δ
tcompile e p = {!!}

tcompileRun : ∀ {σ} → TExpr σ → TVal σ
tcompileRun e = {!!}

checkCompileRun : Expr → Maybe Val
checkCompileRun e = {!!}

v1''' : Maybe Val
v1''' = checkCompileRun e1

v2''' : Maybe Val
v2''' = checkCompileRun e2

v3''' : Maybe Val
v3''' = checkCompileRun e3
