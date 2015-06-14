{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Thorsten Altenkirch

  Lecture 14: Typed Assembly Language

  We continue the theme form the last lecture and look at the
  implementation of a virtual machine and a compiler for the language
  of expressions. We start with an untyped machine which may fail and
  has to do runtime checks (in real life the machine may just crash). 
  Then we introduce "Typed Assembly Language" which can be executed
  without fear and without checking. The compiler from typed
  expressions to typed assembly language is virtually identical to the
  untyped one but uses dependent types to certify the invariant that
  types are preserved. As beofre we use the typechecker together with
  the compiler (actually the code generation part of a compiler) to
  compile and run untyped expressions.

-}
module l14 where

open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import l13 -- import expressions and values

{- We define an untyped assembly language for a stack machine to
   evaluate  untyped expressions. Note that this is tre-structured
   assembly language - this can be translated using gotos by yet
   another pass.
-}
data Code : Set where
  push : Val → Code → Code  -- push a value on the stack
  +M : Code → Code          -- add the top values on the stack
  ≤M : Code → Code          -- compare top values on the stack
  branch : Code → Code → Code -- branch depending on the top value
                              -- instead of gotos the code is tree-structured
  stop : Code -- end of computation

{- the set of stacks - basically a list of values.
   However, I prefer to write stacks backward - that is why I am not
   using stacks. -}
infixl 4 _▹_

data Stack : Set where
  ε : Stack
  _▹_ : Stack → Val → Stack

{- run executes the code, returning the final stack when the
   computation is finished. Note that we are using the partiality
   monad and the operations +v and ≤v from the last lecture which
   check wether their arguments have the right type. 
   Apart from dynamic type errors, run may also fail because there are
   not enough values on the stack.
-}
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
run s stop = just s

{- The compiler is straightforward. We are using "continuation-passing
   style", i.e. the compiler gets the code which is to be exceuted
   after the translation of the expression. This has the advantage
   that we don't have to concatenate code (and hence is more
   efficient) and it is also easier to reason about (even though we
   are not going to prove compiler correctness now. -}
compile : Expr → Code → Code
compile (nat n) c = push (nat n) c
compile (bool b) c = push (bool b) c
compile (e +E e') c = compile e (compile e' (+M c))
  -- here we exploit the continuation passing style.
  -- to compile the who expression we first compile e then e' then add +M
compile (e ≤E e') c = compile e (compile e' (≤M c))
compile (ifE e then e' else e'') c = 
        compile e (branch (compile e' c) (compile e'' c))

{- combining compile and run. compiler correctness would be to show 
   that compileRun is extensionally equal to ⟦_⟧,i.e.

   correct : (e : Expr) compileRun e ≡ ⟦ e ⟧
-}
compileRun : Expr → Maybe Val
compileRun e with run ε (compile e stop)
...             | just (_ ▹ v) = just v
...             | _ = nothing

{- Instead of proving we just test our test cases. -}

v1'' : Maybe Val
v1'' = compileRun e1

v2'' : Maybe Val
v2'' = compileRun e2

v3'' : Maybe Val
v3'' = compileRun e3

{- Next we define "typed assembly language". The type of assembly code
   refers to the type of the stack before and after executing the
   code. -}

{- Stack types are just sequences of value types (defined in the
   previous lecture. -}
data StackTy : Set where
    ε : StackTy
    _▹_ : StackTy → Ty → StackTy

{- Typed stacks are indexed over stack types. -}
data TStack : StackTy → Set where
  ε : TStack ε
  _▹_ : ∀ {Γ σ} → TStack Γ → TVal σ → TStack (Γ ▹ σ)

{- Typed code is indexed by two stacks: the stack it expects and the
   stack after executing it. -}
data TCode : StackTy → StackTy → Set where
  push : ∀ {Γ Δ σ} → TVal σ → TCode (Δ ▹ σ)  Γ → TCode Δ Γ
  +M : ∀ {Γ Δ} → TCode (Δ ▹ nat) Γ → TCode (Δ ▹ nat ▹ nat) Γ
  ≤M : ∀ {Γ Δ} → TCode (Δ ▹ bool) Γ → TCode (Δ ▹ nat ▹ nat) Γ
  branch : ∀ {Γ Δ} → TCode Δ Γ → TCode Δ Γ → TCode (Δ ▹ bool) Γ
  stop : ∀ {Γ} → TCode Γ Γ

{- the typed machine doesn't need to use the Maybe monad becuase the 
   typing invariants are expressed in the indizies. -}
trun : ∀ {Γ Δ} → TStack Γ → TCode Γ Δ → TStack Δ
trun s (push v p) = trun (s ▹ v) p
trun (s ▹ nat n ▹ nat m) (+M p) = trun (s ▹ (nat (n + m))) p
trun (s ▹ nat n ▹ nat m) (≤M p) = trun (s ▹  bool (dec2bool (m ≤? n))) p
trun (s ▹ bool true) (branch p p') = trun s p
trun (s ▹ bool false) (branch p p') = trun s p'
trun s stop = s

{- the typed compiler is virtually identical to the untyped compiler
   but its type makes it clear that the code it generates leaves a
   value corresponding to the type of the expression on the stack.
-}
tcompile : ∀ {Γ Δ σ} → TExpr σ → TCode (Γ ▹ σ) Δ → TCode Γ Δ
tcompile (nat n) c = push (nat n) c
tcompile (bool b) c = push (bool b) c
tcompile (e +E e') c = tcompile e (tcompile e' (+M c))
tcompile (e ≤E e') c = tcompile e (tcompile e' (≤M c))
tcompile (ifE e then e' else e'') c = 
  tcompile e (branch (tcompile e' c) (tcompile e'' c))

{- typed compilation followed by running on the typed machine: -}
tcompileRun : ∀ {σ} → TExpr σ → TVal σ
tcompileRun e with trun ε (tcompile e stop)
...             | (_ ▹ v) = v

{- combining this with the type checker we obtan yet another way to
   execute untyped expression in an efficient and fast way. -}
checkCompileRun : Expr → Maybe Val
checkCompileRun e = infer e >>= λ c → return (⌊ tcompileRun (Check.te c)  ⌋v) 