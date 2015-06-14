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

fstV : Val → Maybe Val
fstV (v , v') = just v
fstV _ = nothing

sndV : Val → Maybe Val
sndV (v , v') = just v'
sndV _ = nothing

{- The evaluator. We use Scott-brackets (⟦ = \[[, ⟧ = \]]) as it is
   tradition to mark the borderline between syntax and semantics.
   Evaluation of an expression may return a value of fail. -}
⟦_⟧ : Expr → Maybe Val
⟦ nat n ⟧ = return (nat n)
⟦ bool b ⟧ = return (bool b)
⟦ e , e' ⟧ =  ⟦ e ⟧ >>= λ v → 
             ⟦ e' ⟧ >>= λ v' →
             just (v , v')
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
⟦ fst e ⟧ = ⟦ e ⟧ >>= λ v → fstV v
⟦ snd e ⟧ = ⟦ e ⟧ >>= λ v → sndV v


{- Evaluation the examples: -}

v1 : Maybe Val -- just (nat 5)
v1 = ⟦ e1 ⟧

v2 : Maybe Val -- just (bool true)
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

{- typed expressions -}
data TExpr : Ty → Set where
  nat : ℕ → TExpr nat
  bool : Bool → TExpr bool
  _,_ : ∀ {σ τ} → TExpr σ → TExpr τ → TExpr (σ × τ)
  _+E_ : TExpr nat → TExpr nat → TExpr nat
  _≤E_ : TExpr nat → TExpr nat → TExpr bool
  ifE_then_else_ : {σ : Ty} → TExpr bool → TExpr σ → TExpr σ → TExpr σ
  fst : ∀ {σ τ} → TExpr (σ × τ) → TExpr σ 
  snd : ∀ {σ τ} → TExpr (σ × τ) → TExpr τ


{- the typed evaluator
   doesn't need to use the Maybe monad because it will never fail. -}
⟦_⟧T : {σ : Ty} → TExpr σ → TVal σ
⟦ nat n ⟧T = nat n
⟦ bool b ⟧T = bool b
⟦ e , e' ⟧T = ⟦ e ⟧T , ⟦ e' ⟧T
⟦ e +E e' ⟧T with ⟦ e ⟧T | ⟦ e' ⟧T
...         | nat m | nat n = nat (m + n)
⟦ e ≤E e' ⟧T with ⟦ e ⟧T | ⟦ e' ⟧T
...             | nat m | nat n = bool (dec2bool (m ≤? n))
⟦ ifE e then e' else e'' ⟧T with ⟦ e ⟧T 
...                           | bool b = if b then ⟦ e' ⟧T else ⟦ e'' ⟧T 
⟦ fst e ⟧T with ⟦ e ⟧T
...        |   v , v' = v
⟦ snd e ⟧T with ⟦ e ⟧T
...        |   v , v' = v'


{- A forgetful map from typed expressions to untyped expressions -}
⌊_⌋ : {σ : Ty} → TExpr σ → Expr
⌊ nat n ⌋ = nat n
⌊ bool b ⌋ = bool b
⌊ e , e' ⌋ = ⌊ e ⌋ , ⌊ e' ⌋
⌊ e +E e' ⌋ = ⌊ e ⌋ +E ⌊ e' ⌋
⌊ e ≤E e' ⌋ = ⌊ e ⌋ ≤E ⌊ e' ⌋
⌊ ifE e then e' else e'' ⌋ =  ifE ⌊ e ⌋ then ⌊ e' ⌋ else ⌊ e'' ⌋
⌊ fst e ⌋ = fst ⌊ e ⌋
⌊ snd e ⌋ = snd ⌊ e ⌋

infix 0 _≡Ty?_

inj×₁ : ∀ {σ σ' τ τ'} → σ × τ ≡ σ' × τ' → σ ≡ σ'
inj×₁ refl = refl

inj×₂ : ∀ {σ σ' τ τ'} → σ × τ ≡ σ' × τ' → τ ≡ τ'
inj×₂ refl = refl

{- equality of types is clearly decidable -}
_≡Ty?_ : (σ τ : Ty) → Dec (σ ≡ τ)
nat ≡Ty? nat = yes refl
nat ≡Ty? bool = no (λ ())
nat ≡Ty? _ × _ = no (λ ())
bool ≡Ty? nat =  no (λ ())
bool ≡Ty? bool = yes refl
bool ≡Ty? _ × _ =  no (λ ())
_ × _ ≡Ty? nat =  no (λ ())
_ × _ ≡Ty? bool =  no (λ ())
σ × τ ≡Ty? σ' × τ' with σ ≡Ty? σ'
.σ' × τ ≡Ty? σ' × τ' | yes refl with τ ≡Ty? τ'
.σ' × .τ ≡Ty? σ' × τ | yes refl | yes refl = yes refl
.σ' × τ ≡Ty? σ' × τ' | yes refl | no ¬p = no (λ q → ¬p (inj×₂ q))
σ × τ ≡Ty? σ' × τ' | no ¬p = no (λ q → ¬p (inj×₁ q))

{- The result of checking an expression e is a record containing: -}
record Check (e : Expr) : Set where
  constructor check
  field 
    σ : Ty                -- a type
    te : TExpr σ          -- a typed expression
    te≡e : ⌊ te ⌋ ≡ e    -- if we forget the types we recover e

{- This is the first time we use records in Agda.
   Look up the reference manual for a decription of records in Agda. -}

open Check

{- We implement type inference by recursion over the expression. -}
infer : (e : Expr) → Maybe (Check e)
infer (nat n) = just (check nat (nat n) refl)
infer (bool b) = just (check bool (bool b) refl)
infer (e , e') with infer e | infer e'
infer (.(⌊ te ⌋) , .(⌊ te' ⌋)) | just (check σ te refl) | just (check τ te' refl) 
      = just (check (σ × τ) (te , te') refl)
infer (e , e') | _ |  _ = nothing
infer (e +E e') with infer e | infer e'
infer (.(⌊ te ⌋) +E .(⌊ te' ⌋)) | just (check nat te refl) | just (check nat te' refl) 
      = just (check nat (te +E te') refl)
infer (e +E e') | _ |  _ = nothing
{- ≤ uses the same technique -}
infer (e ≤E e') with infer e | infer e'
infer (.(⌊ te ⌋) ≤E .(⌊ te' ⌋)) | just (check nat te refl) | just (check nat te' refl) 
      = just (check bool (te ≤E te') refl)
infer (e ≤E e') | _ |  _ = nothing
{- if-then-else also has to make sure that both branches have the same
   type, which is the type of the result. -}
infer (ifE e then e' else e'') with infer e | infer e' | infer e''
infer (ifE .(⌊ te ⌋) then .(⌊ te' ⌋) else .(⌊ te'' ⌋))  
      | just (check bool te refl) | just (check σ te' refl) | just (check σ' te'' refl) with σ ≡Ty? σ'
infer (ifE .(⌊ te ⌋) then .(⌊ te' ⌋) else .(⌊ te'' ⌋))  
      | just (check bool te refl) | just (check σ te' refl) | just (check .σ te'' refl)    | yes refl 
      = just (check σ (ifE te then te' else te'') refl)
infer (ifE .(⌊ te ⌋) then .(⌊ te' ⌋) else .(⌊ te'' ⌋))  
      | just (check bool te refl) | just (check σ te' refl) | just (check σ' te'' refl)    | no _     = nothing
infer (ifE e then e' else e'') | _ | _ | _ = nothing
infer (fst e) with infer e
infer (fst .(⌊ te ⌋)) | just (check (σ × τ) te refl) = just (check σ (fst te) refl)
infer (fst _)  | _ = nothing
infer (snd e) with infer e
infer (snd .(⌊ te ⌋)) | just (check (σ × τ) te refl) = just (check τ (snd te) refl)
infer (snd _)  | _ = nothing

{- A safe evaluator -}

{- We can also forget the types of typed values -}
⌊_⌋v : {σ : Ty} → TVal σ → Val
⌊ nat n ⌋v = nat n
⌊ bool b ⌋v = bool b
⌊ v , v' ⌋v = ⌊ v  ⌋v , ⌊ v' ⌋v

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

data Code : Set where
  push : Val → Code → Code
  +M : Code → Code
  ≤M : Code → Code
  branch : Code → Code → Code
  stop : Code
  pairM : Code → Code
  fstM : Code → Code
  sndM : Code → Code

data Stack : Set where
  ε : Stack
  _▹_ : Stack → Val → Stack

run : Stack → Code → Maybe Stack
run s (push v p) = run (s ▹ v) p
run ((s ▹ v) ▹ v') (+M p) = v +v v' >>= λ v+v' → run (s ▹ v+v') p
run _ (+M _) = nothing
run ((s ▹ v) ▹ v') (≤M p) = v ≤v v' >>= λ v≤v' → run (s ▹ v≤v') p
run _ (≤M _) = nothing
run (s ▹ bool true) (branch p p') = run s p
run (s ▹ bool false) (branch p p') = run s p'
run (s ▹ _) (branch _ _) = nothing
run _ (branch _ _) = nothing
run ((s ▹ v) ▹ v') (pairM p) = run (s ▹ (v , v')) p 
run _ (pairM _) = nothing
run (s ▹ (v , v')) (fstM p) = run (s ▹ v) p  
run _ (fstM _) = nothing
run (s ▹ (v , v')) (sndM p) = run (s ▹ v') p  
run _ (sndM _) = nothing
run s stop = just s


compile : Expr → Code → Code
compile (nat n) c = push (nat n) c
compile (bool b) c = push (bool b) c
compile (e +E e') c = compile e (compile e' (+M c))
compile (e ≤E e') c = compile e (compile e' (≤M c))
compile (ifE e then e' else e'') c = 
        compile e (branch (compile e' c) (compile e'' c))
compile (e , e') c = compile e (compile e' (pairM c))
compile (fst e) c = compile e (fstM c)
compile (snd e) c = compile e (sndM c)

compileRun : Expr → Maybe Val
compileRun e with run ε (compile e stop)
...             | just (_ ▹ v) = just v
...             | _ = nothing


{-
--- typed assembly language
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

trun : ∀ {Γ Δ} → TStack Γ → TCode Γ Δ → TStack Δ
trun s (push v p) = trun (s ▹ v) p
trun (s ▹ nat n ▹ nat m) (+M p) = trun (s ▹ (nat (n + m))) p
trun (s ▹ nat n ▹ nat m) (≤M p) = trun (s ▹  bool (dec2bool (m ≤? n))) p
trun (s ▹ bool true) (branch p p') = trun s p
trun (s ▹ bool false) (branch p p') = trun s p'
trun s stop = s

tcompile : ∀ {Γ Δ σ} → TExpr σ → TCode (Γ ▹ σ) Δ → TCode Γ Δ
tcompile (nat n) c = push (nat n) c
tcompile (bool b) c = push (bool b) c
tcompile (e +E e') c = tcompile e (tcompile e' (+M c))
tcompile (e ≤E e') c = tcompile e (tcompile e' (≤M c))
tcompile (ifE e then e' else e'') c = 
  tcompile e (branch (tcompile e' c) (tcompile e'' c))

tcompileRun : ∀ {σ} → TExpr σ → TVal σ
tcompileRun e with trun ε (tcompile e stop)
...             | (_ ▹ v) = v

checkCompileRun : Expr → Maybe Val
checkCompileRun e = infer e >>= λ c → return (⌊ tcompileRun (Check.te c)  ⌋v) 
-}