{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Thorsten Altenkirch

  Lecture 11: Inductive relations

  In this lecture we show how relations can be defined
  inductively. The idea is that we give constructors for derivations
  defining a dependent type like Vec or Fin.

  We look at two examples: the ≤-relation (less-or-equal) on the
  natural numbers and two different definitions of derivations for
  propositional logic with implication only. We show that ≤ is an
  partial order and that the combinatory version of propositional
  logic (with the combinators S and K) is equivalent to one with an
  introduction rule for implication.

-}
module l11 where

open import Data.Nat hiding (_≤_ ; _≤?_ ; _<_)
open import Relation.Binary.PropositionalEquality -- defines ≡ 
open import Relation.Nullary
open import Data.String

{- inductive defn of ≤ - there are two ways to show m ≤ n:
    z≤n : zero is less-or-equal any number.
    s≤s : if m is less-or equal n them suc m is less-or-equal suc n.
    These are the only ways to show m ≤ n.
 -}

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

{- examples -}

2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

{- Note that there wasn't much choice deriving 2≤4. Indeed we just
   have to type C-c C-r three times. -}

{- How to prove a negative result? 
   We use pattern matching until we obtain an obviously impossible
   pattern. 
-}

¬4≤2 : ¬ 4 ≤ 2
¬4≤2 (s≤s (s≤s ()))

{- We want to show that ≤ is a partial order, i.e. it is reflexive,
   transitive and antisymmetric. -}  

{- we prove reflexivity by a simple induction over the natural
   numbers. -}

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s (≤-refl {n})

{- transitivity and antisymmetry both require an analysis of the input
   derivation using pattern matching. -}

≤-trans : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
≤-trans z≤n m≤n = z≤n
≤-trans (s≤s m≤n) (s≤s n≤n') = s≤s (≤-trans m≤n n≤n')

≤-asym : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
≤-asym z≤n z≤n = refl
≤-asym (s≤s m≤n) (s≤s m≤n') = cong suc (≤-asym m≤n m≤n')

{- Additionally we can prove something about the proofs of ≤, namely
   that they contain no information. We can show that any two proof of
   m ≤ n are the same. Note that this similar to the uniqueness of
   identy proofs we showed in the last lecture. -}

≤-unique : {m n : ℕ} → (p q : m ≤ n) → p ≡ q
≤-unique z≤n z≤n = refl
≤-unique (s≤s m≤n) (s≤s m≤n') = cong s≤s (≤-unique m≤n m≤n')

{- Finally we establish that ≤ is decidable: -}

{- To deal with the negative successor case we need to invert the s≤s
   constructor, which is easy using pattern matching. -}
s≤s-inv : ∀ {m n} → suc m ≤ suc n → m ≤ n
s≤s-inv (s≤s m≤n) = m≤n

{- decidablity can be derived by analyzing the numbers. The structure
   is similar to the decidability of equality for natural numbers we
   did last week. -}

_≤?_ : (m n : ℕ) → Dec (m ≤ n)
zero ≤? n = yes z≤n
suc n ≤? zero = no (λ ())
suc n ≤? suc n' with n ≤? n'
suc n ≤? suc n' | yes p = yes (s≤s p)
suc n ≤? suc n' | no ¬p = no (λ x → ¬p (s≤s-inv x))

{- We shall now use inductively defined relations to develop some
   basic metatheory, i.e. we are going to prove something *about* a
   logic (instead of within). As an example we use a very small logic:
   Propositional Logic with implication only. -}

{- First we formalize the syntax of formulas: -}
data Formula : Set where
  Atom : String → Formula
  _⇒_ : (A B : Formula) → Formula

infixr 6 _⇒_ 

{- Here is an example formula - the translation of (P -> Q) -> P -}
example : Formula
example = ((Atom "P") ⇒ (Atom "Q")) ⇒ Atom "P"

{- We also need to define contexts of assumptions which are basically
   lists of formulas. However, we are not using Lists since the
   convention is that contexts are written backwards. -}
data Context : Set where
  ε : Context
  _·_ : (Γ : Context) → (A : Formula) → Context

infix 4 _⊢sk_
infix 4 _⊢_
infixl 5 _·_

-- ⊢ = \vdash (pronounced turnstyle)

{- We define the relation ⊢ , where Γ ⊢ A means that the formular A is
   derivable from the assumptions Γ. 
   What are the basic proof rules for propositional logic?-}

data _⊢_ : Context → Formula → Set where
  ass : ∀ {Γ A} → Γ · A ⊢ A
  {- we can prove a formula is we have assumed it. -}
  weak : ∀ {Γ A B} → Γ ⊢ A → Γ · B ⊢ A
  {- we can ignore an assumption. -}
  app : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  {- this is also called the modus ponens. -}
  abs : ∀ {Γ A B} → Γ · A ⊢ B → Γ ⊢ A ⇒ B
  {- To prove A implies B, we assume A and prove B. -}

{- As two examples we derive the basic combinators S and K. -}
K' : ∀ {Γ A B} → Γ ⊢ A ⇒ B ⇒ A
K' = abs (abs (weak ass))

S' : ∀ {Γ A B C} → Γ ⊢ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
S' = abs (abs (abs (app (app (weak (weak ass)) ass)
         (app (weak ass) ass))))

{- The main theorem we are going to prove is that K and S can be used
   as replacement for the abstraction rule.
   Formally we define an alternative derivation relation ⊢sk where 
   the abstraction rule is replaced by axioms for S and K. -}

data _⊢sk_ : Context → Formula → Set where
  ass : ∀ {Γ A} → Γ · A ⊢sk A
  weak : ∀ {Γ A B} → Γ ⊢sk A → Γ · B ⊢sk A
  app : ∀ {Γ A B} → Γ ⊢sk A ⇒ B → Γ ⊢sk A → Γ ⊢sk B
  K : ∀ {Γ A B} → Γ ⊢sk A ⇒ B ⇒ A
  S : ∀ {Γ A B C} → Γ ⊢sk (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
 
{- It is easy to show that provability ising ⊢sk implies ⊢ since
   we have already established S and K.
   We prove this by induction over the derivation of ⊢sk.
-}
⊢sk→⊢ : ∀ {Γ A} → Γ ⊢sk A → Γ ⊢ A
⊢sk→⊢ ass = ass
⊢sk→⊢ (weak d) = weak (⊢sk→⊢ d)
⊢sk→⊢ (app d d') = app (⊢sk→⊢ d) (⊢sk→⊢ d')
⊢sk→⊢ K = K'
⊢sk→⊢ S = S'

{- To show the other direction we need to show that the abstraction
   rule is derivable for ⊢sk.
   As a first step we show that A → A is provable.
-}
I : ∀ {Γ A} → Γ ⊢sk A ⇒ A
I {Γ} {A} = app (app S K) (K {B = A})

{- To show the abstraction rule for SK we analyze the possible proofs
   of the proof with the added assumption.
   The combinators I, K , S are precisely what is needed for the
   assumption, weakeneing and application rule. This explains the
   choice especially of the S combinator.
   The last two lines mean that we can prove S and K with an extra
   assumption using K.
-}
abs' : ∀ {Γ A B} → Γ · A ⊢sk B → Γ ⊢sk A ⇒ B
abs' ass = I
abs' (weak d) = app K d
abs' (app d d') = app (app S (abs' d)) (abs' d')
abs' K = app K K
abs' S = app K S

{- We are now ready to prove the other direction 
   by induction over the derivation. -}
⊢→⊢sk : ∀ {Γ A} → Γ ⊢ A → Γ ⊢sk A
⊢→⊢sk ass = ass
⊢→⊢sk (weak d) = weak (⊢→⊢sk d)
⊢→⊢sk (app d d') = app (⊢→⊢sk d) (⊢→⊢sk d')
⊢→⊢sk (abs d) = abs' (⊢→⊢sk d)
