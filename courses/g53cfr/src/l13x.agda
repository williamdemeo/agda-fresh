{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Thorsten Altenkirch

  Lecture 13: Evaluator and type checker
  (w.o. record constructors)

  In this lecture we investigate an evaluator for a simple language of
  expressions over natural numbers and booleans. We first implement an
  untyped evaluator (which may fail and is slow) and then an evaluator
  for a typed language which will always succeed and is faster. To go
  from an untyped expression to a typed expression we implement a type
  checker. The type checker may also fail but this is early (before
  evaluation) and doesn't affect the efficiency of evaluations.

-}
module l13x where

open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

{- an untyped language of expressions -}

infix 3 _≤E_
infix 4 _+E_

data Expr : Set where
  nat : ℕ → Expr
  bool : Bool → Expr
  _+E_ : Expr → Expr → Expr
  _≤E_ : Expr → Expr → Expr
  ifE_then_else_ : Expr → Expr → Expr → Expr
  
{- Examples of expressions: -}

e1 : Expr -- if 3 ≤ 4 then 4 + 1 else 0
e1 = ifE (nat 3) ≤E (nat 4) then (nat 4) +E (nat 1) else (nat 0)

e2 : Expr -- 3 ≤ 4 + 5
e2 = (nat 3) ≤E (nat 4) +E (nat 5)

e3 : Expr -- (3 ≤ 4) + 5
e3 = ((nat 3) ≤E (nat 4)) +E (nat 5)

{- The result of evaluating an expression is a value -}

data Val : Set where
  nat : ℕ → Val
  bool : Bool → Val

{- To accomodate errors we introduce the Maybe monad.
   A Monad M is an operation on Sets such that M A is the type of
   computations over A. In the case of Maybe a computation is
   something that may go wrong (i.e. returns nothing).

   Each monad comes with two functions:

   return : {A : Set} → A → M A
   turns a value into a (trivial) computation.

   _>>=_ : {A B : Set} → M A → (A → M B) → M B
   (bind) m >>= f runs first the computation m and if it returns a
   value runs f in it. The effects are a combination of running both
   computations.
-}

-- for Maybe return is just (no error)
return : {A : Set} → A → Maybe A
return a = just a

infix 2 _>>=_

-- bind does error propagation
_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
just a >>= f = f a
nothing >>= f = nothing

{- To implement the evaluator we implement some convenience
   functions. -}

{- Addition of two values has to check wether the values are indeed
   numbers -}
_+v_ : Val → Val → Maybe Val
nat m +v nat n = return (nat (m + n))
_ +v _ = nothing

{- dec2bool coerces decidability into bool by forgetting the
   evidence. -}
dec2bool : {A : Set} → Dec A → Bool
dec2bool (yes p) = true
dec2bool (no ¬p) = false

{- This is used to implement ≤ for values. As +v this has to check
   wether the arguments are numbers. -}
_≤v_ : Val → Val → Maybe Val
nat m ≤v nat n = return (bool (dec2bool (m ≤? n)))
_ ≤v _ = nothing

{- if-then-else for values. May return an error if the first argument
   is not a boolean.
-}
ifV_then_else_ : Val → Val → Val → Maybe Val
ifV bool b then v else v' = return (if b then v else v')
ifV _ then _ else _ = nothing

{- The evaluator. We use Scott-brackets (⟦ = \[[, ⟧ = \]]) as it is
   tradition to mark the borderline between syntax and semantics.
   Evlauation an expression may return a value of fail. -}
⟦_⟧ : Expr → Maybe Val
⟦ nat n ⟧ = return (nat n)
⟦ bool b ⟧ = return (bool b)
⟦ e +E e' ⟧ = ⟦ e ⟧ >>= λ v → 
             ⟦ e' ⟧ >>= λ v' →
             v +v v'
{- In Haskell we would use "do" syntax:
   do v <- ⟦ e ⟧
      v' <- ⟦ e' ⟧
      v +v v' 
-}
⟦ e ≤E e' ⟧ = ⟦ e ⟧ >>= λ v → 
             ⟦ e' ⟧ >>= λ v' →
             v ≤v v'
⟦ ifE e then e' else e'' ⟧ = ⟦ e ⟧ >>= λ v → 
                            ⟦ e' ⟧ >>= λ v' →
                            ⟦ e'' ⟧ >>= λ v'' →
                            ifV v then v' else v''


{- Evaluation the examples: -}

v1 : Maybe Val -- just (nat 5)
v1 = ⟦ e1 ⟧

v2 : Maybe Val -- just (bool true)
v2 = ⟦ e2 ⟧

v3 : Maybe Val
v3 = ⟦ e3 ⟧ -- nothing

{- We do everything again but this time for a typed language. -}

{- the types -}
data Ty : Set where
  nat : Ty
  bool : Ty

{- typed values -}
data TVal : Ty → Set where
  nat : ℕ → TVal nat
  bool : Bool → TVal bool

{- typed expressions -}
data TExpr : Ty → Set where
  nat : ℕ → TExpr nat
  bool : Bool → TExpr bool
  _+E_ : TExpr nat → TExpr nat → TExpr nat
  _≤E_ : TExpr nat → TExpr nat → TExpr bool
  ifE_then_else_ : {σ : Ty} → TExpr bool → TExpr σ → TExpr σ → TExpr σ

{- the typed evaluator
   doesn't need to use the Maybe monad because it will never fail. -}
⟦_⟧T : {σ : Ty} → TExpr σ → TVal σ
⟦ nat n ⟧T = nat n
⟦ bool b ⟧T = bool b
⟦ e +E e' ⟧T with ⟦ e ⟧T | ⟦ e' ⟧T
...         | nat m | nat n = nat (m + n)
⟦ e ≤E e' ⟧T with ⟦ e ⟧T | ⟦ e' ⟧T
...             | nat m | nat n = bool (dec2bool (m ≤? n))
⟦ ifE e then e' else e'' ⟧T with ⟦ e ⟧T 
...                           | bool b = if b then ⟦ e' ⟧T else ⟦ e'' ⟧T 

{- But what to do if just have got an untyped expression (maybe read
   from a file)? We use a type checker to lift an untyped expression
   to an equivalent typed expression (or fail).
-}


{- A forgetful map from typed expressions to untyped expressions -}
⌊_⌋ : {σ : Ty} → TExpr σ → Expr
⌊ nat n ⌋ = nat n
⌊ bool b ⌋ = bool b
⌊ e +E e' ⌋ = ⌊ e ⌋ +E ⌊ e' ⌋
⌊ e ≤E e' ⌋ = ⌊ e ⌋ ≤E ⌊ e' ⌋
⌊ ifE e then e' else e'' ⌋ =  ifE ⌊ e ⌋ then ⌊ e' ⌋ else ⌊ e'' ⌋

{- equality of types is clearly decidable -}
_≡Ty?_ : (σ τ : Ty) → Dec (σ ≡ τ)
nat ≡Ty? nat = yes refl
nat ≡Ty? bool = no (λ ())
bool ≡Ty? nat = no (λ ())
bool ≡Ty? bool = yes refl

{- The result of checking an expression e is a record containing: -}
record Check (e : Expr) : Set where
--  constructor check
  field 
    σ : Ty                -- a type
    te : TExpr σ          -- a typed expression
    te≡e : ⌊ te ⌋ ≡ e    -- if we forget the types we recover e

check : ∀ {e} → (σ : Ty)(te : TExpr σ) → ⌊ te ⌋ ≡ e → Check e
check σ te te≡e = record {σ = σ; te = te; te≡e = te≡e}

{- This is the first time we use records in Agda.
   Look up the reference manual for a decription of records in Agda. -}

open Check
{- Records also use modules which hide the projection functions. By
   opening it we have direct access to the projection functions
   corresponding to the field names.
   E.g. we have 
   σ : Check e → Ty
   te : (c : Check e) → TExpr (σ c)
-}

{- We implement type inference by recursion over the expression. -}
infer : (e : Expr) → Maybe (Check e)
infer (nat n) = just (check nat (nat n) refl)
infer (bool b) = just (check bool (bool b) refl)
infer (e +E e') with infer e | infer e' 
infer (e +E e') | just c | just c' with σ c | σ c' | te c | te c' | te≡e c | te≡e c'
infer (.(⌊ te ⌋) +E .(⌊ te' ⌋)) | just c | just c' | nat | nat | te | te' | refl | refl 
      = just (check nat (te +E te') refl)
infer (e +E e')                  | just c | just c' | _   | _   | _  | _   | _    | _ 
      = nothing
infer (e +E e') | _ |  _ = nothing
infer (e ≤E e') with infer e | infer e' 
infer (e ≤E e') | just c | just c' with σ c | σ c' | te c | te c' | te≡e c | te≡e c'
infer (.(⌊ te ⌋) ≤E .(⌊ te' ⌋)) | just c | just c' | nat | nat | te | te' | refl | refl 
      = just (check bool (te ≤E te') refl)
infer (e ≤E e')                  | just c | just c' | _   | _   | _  | _   | _    | _ 
      = nothing
infer (e ≤E e') | _ |  _ = nothing
infer (ifE e then e' else e'') with infer e | infer e' | infer e''
infer (ifE e then e' else e'') |    just c  | just c'  | just c''  with σ c | σ c' | σ c'' | te c | te c'  | te c'' | te≡e c | te≡e c' | te≡e c''
infer (ifE .(⌊ te ⌋) then .(⌊ te' ⌋) else .(⌊ te'' ⌋)) | just c | just c' | just c'' | bool | σ | σ' | te | te' | te'' | refl | refl | refl with σ ≡Ty? σ'
infer (ifE .(⌊ c'' ⌋) then .(⌊ te' ⌋) else .(⌊ te'' ⌋)) | just c | just c' | just c'' | bool | .σ' | σ' | te | te' | te'' | refl | refl | refl | yes refl 
      = just (check σ' (ifE te then te' else te'') refl)
infer (ifE .(⌊ c'' ⌋) then .(⌊ te' ⌋) else .(⌊ te'' ⌋)) | just c | just c' | just c'' | bool | σ | σ' | te | te' |  te'' | refl | refl | refl | no ¬p 
      = nothing
infer (ifE e then e' else e'') | just c | just c' | just c'' | _ | _ | _ |  _ | _ | _ | _ | _ | _ = nothing
infer (ifE e then e' else e'') |    _       | _        | _         = nothing

{- We can also forget the types of typed values -}
⌊_⌋v : {σ : Ty} → TVal σ → Val
⌊ nat n ⌋v = nat n
⌊ bool b ⌋v = bool b

{- We implement a safe evaluator which has the same type as the
   untyped evaluator. It exploits the type checker to first produce a
   typed expression (or fail) and then runs the fast and safe typed
   evaluator. 
-}
⟦_⟧s : Expr → Maybe Val
⟦ e ⟧s = infer e >>= λ c → return (⌊ ⟦ Check.te c ⟧T ⌋v) 

{- For our examples that safe evaluator produces the same results: -}

v1' : Maybe Val
v1' = ⟦ e1 ⟧s

v2' : Maybe Val
v2' = ⟦ e2 ⟧s

v3' : Maybe Val
v3' = ⟦ e3 ⟧s

{- Is this always the case ? -}
