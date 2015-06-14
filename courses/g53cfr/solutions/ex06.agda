{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Thorsten Altenkirch

  Exercise 6: Inductive relations
  Deadline: 12/3/10

  Use the coursework submission (id: 272)) system to submit the coursework
  after demonstrating it in the lab to me or Darin.
  
  Prove the following propositions by
  completing the sheds { .. }.

  Note that not all propositions may be provable. If you think that a
  proposition is unprovable clearly mark this one by adding a line:
  -- impossible.

-}

module ex06 where

open import Data.Nat
open import Relation.Nullary
open import Data.String
open import Relation.Binary.PropositionalEquality

{- Even

  we inductively define the predicate even.

 -}

data Even : ℕ → Set where
  zero : Even zero
  sucsuc : ∀ {n} → Even n → Even (suc (suc n))

{- show that 4 is even. -}

even4 : Even 4
even4 = sucsuc (sucsuc zero)

{- show that 3 is not even. -}

¬even3 : ¬ (Even 3)
¬even3 (sucsuc ())

{- show that sucsuc is invertible -}

inv-sucsuc : ∀ {n} → Even (suc (suc n)) → Even n 
inv-sucsuc (sucsuc evenn) = evenn

{- show that there is at most one proof of even. -}

even-unique : ∀ {m} → (p q : Even m) → p ≡ q
even-unique zero zero = refl
even-unique (sucsuc p) (sucsuc q) = cong sucsuc (even-unique p q)

{- show that even is decidable. -}

even? : (n : ℕ) → Dec (Even n)
even? zero = yes zero
even? (suc zero) = no (λ ())
even? (suc (suc n)) with even? n
even? (suc (suc n)) | yes p = yes (sucsuc p)
even? (suc (suc n)) | no ¬p = no (λ x → ¬p (inv-sucsuc x))

{- Combinatoric logic: we extend propositional logic by conjunction:  -}

data Formula : Set where
  Atom : String → Formula
  _⇒_ : (A B : Formula) → Formula
  _∧_ :  (A B : Formula) → Formula

data Context : Set where
  ε : Context
  _·_ : (Γ : Context) → (A : Formula) → Context

infixl 7 _∧_
infixr 6 _⇒_ 
infix 4 _⊢sk_
infix 4 _⊢_
infixl 5 _·_

data _⊢_ : Context → Formula → Set where
  ass : ∀ {Γ A} → Γ · A ⊢ A
  weak : ∀ {Γ A B} → Γ ⊢ A → Γ · B ⊢ A
  app : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  abs : ∀ {Γ A B} → Γ · A ⊢ B → Γ ⊢ A ⇒ B
  {- To prove a conjuction we prove both components -}
  pair : ∀ {Γ A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ∧ B
  {- To use a conjunction is the same as assuming both components -}
  elim : ∀ {Γ A B C} → Γ · A · B ⊢ C → Γ · A ∧ B ⊢ C

{- In combinatory logic we add three combinators pair, fst and snd -}

data _⊢sk_ : Context → Formula → Set where
  ass : ∀ {Γ A} → Γ · A ⊢sk A
  weak : ∀ {Γ A B} → Γ ⊢sk A → Γ · B ⊢sk A
  app : ∀ {Γ A B} → Γ ⊢sk A ⇒ B → Γ ⊢sk A → Γ ⊢sk B
  K : ∀ {Γ A B} → Γ ⊢sk A ⇒ B ⇒ A
  S : ∀ {Γ A B C} → Γ ⊢sk (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
  pair : ∀ {Γ A B} → Γ ⊢sk A ⇒ B ⇒ A ∧ B
  fst : ∀ {Γ A B} → Γ ⊢sk A ∧ B ⇒ A
  snd : ∀ {Γ A B} → Γ ⊢sk A ∧ B ⇒ B

{- Show that the two derivation relations are equivalent.

  Hint: You are welcome to reuse (and extend) proofs from l11.agda 
-}

pair' : ∀ {Γ A B} → Γ ⊢ A ⇒ B ⇒ A ∧ B
pair' = abs (abs (pair (weak ass) ass))

fst' : ∀ {Γ A B} → Γ ⊢ A ∧ B ⇒ A
fst' = abs (elim (weak ass))

snd' : ∀ {Γ A B} → Γ ⊢ A ∧ B ⇒ B
snd' = abs (elim ass)

I : ∀ {Γ A} → Γ ⊢sk A ⇒ A
I {Γ} {A} = app (app S K) (K {B = A})

K' : ∀ {Γ A B} → Γ ⊢ A ⇒ B ⇒ A
K' = abs (abs (weak ass))

S' : ∀ {Γ A B C} → Γ ⊢ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
S' = abs (abs (abs (app (app (weak (weak ass)) ass)
         (app (weak ass) ass))))

abs' : ∀ {Γ A B} → Γ · A ⊢sk B → Γ ⊢sk A ⇒ B
abs' ass = I
abs' (weak d) = app K d
abs' (app d d') = app (app S (abs' d)) (abs' d')
abs' K = app K K
abs' S = app K S
abs' pair = app K pair
abs' fst = app K fst
abs' snd = app K snd

elim' :  ∀ {Γ A B C} → Γ · A · B ⊢sk C → Γ · A ∧ B ⊢sk C
elim' d = app (app (weak (abs' (abs' d))) (app fst ass)) (app snd ass)

⊢sk→⊢ : ∀ {Γ A} → Γ ⊢sk A → Γ ⊢ A
⊢sk→⊢ ass = ass
⊢sk→⊢ (weak d) = weak (⊢sk→⊢ d)
⊢sk→⊢ (app d d') = app (⊢sk→⊢ d) (⊢sk→⊢ d')
⊢sk→⊢ K = K'
⊢sk→⊢ S = S'
⊢sk→⊢ pair = pair'
⊢sk→⊢ fst = fst'
⊢sk→⊢ snd = snd'

⊢→⊢sk : ∀ {Γ A} → Γ ⊢ A → Γ ⊢sk A
⊢→⊢sk ass = ass
⊢→⊢sk (weak d) = weak (⊢→⊢sk d)
⊢→⊢sk (app d d') = app (⊢→⊢sk d) (⊢→⊢sk d')
⊢→⊢sk (abs d) = abs' (⊢→⊢sk d)
⊢→⊢sk (pair d d') = app (app pair (⊢→⊢sk d)) (⊢→⊢sk d')
⊢→⊢sk (elim d) = elim' (⊢→⊢sk d)

