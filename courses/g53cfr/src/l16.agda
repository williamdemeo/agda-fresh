{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Thorsten Altenkirch

  Lecture 16: More on coinductive definitions

  In this lecture we continue the topic of coinductive
  definitions. We cover the following aspects

  1 We discuss why *co*-inductive definitions can be
    considered as the dual ("mirror image") of inductive definitions. 
  2 We compare our definition of extensional equality for
    streams (_≈_) with the traditional definition as the "largest
    bisimulation". 
  3 We show that Streams over A are "extensionally isomorphic" to
    functions over the natural numbers. This is a general phenomen
    (all coinductive types can be encoded using functions over the
    natural numbers).
  4 We look at an example where we mix inductive and coinductive
    definitions - stream processors as a representation of functions
    over streams.

-}
module l16 where

open import Coinduction
open import Data.Nat hiding (fold)
open import Data.List hiding (unfold)
open import Relation.Binary.PropositionalEquality
open import l15 hiding (tail)

{- 1 Coinductive types as the dual of inductive types. -}

{- For inductive types like lists we can define a "fold"-combinator 
   which is a universal combinator to define recursive functions.
   The type of fold can be derived form the constructors of list 
   and gives rise to a function form lists into another set.

   fold n c replaces each [] by n and each _∷_ by c. This is only
   possible if the list is finite.
-}

fold : {A B : Set} → B → (A → B → B) → List A → B
fold n c [] = n
fold n c (x ∷ xs) = c x (fold n c xs)

{- For coinductive types we start not with the constructors but with
   the destructors - in the case of streams head and tail. -}

head : ∀ {A} → Stream A → A
head (a ∷ as) = a

tail : ∀ {A} → Stream A → Stream A
tail (a ∷ as) = ♭ as

{- Instead of fold we a combinator "unfold" which is universal for
   corecursive definitions. The type of unfold is based on the
   destructors and gives rise to a function from a given set to the
   set of streams.

   unfold h t b produces a stream such that any program which uses
   only h and t on B behaves the same way if we replace h by head and
   t by tail.
-}

unfold : {A B : Set} → (B → A) → (B → B) → B → Stream A
unfold h t b = h b ∷ (♯ unfold h t (t b))

{- 2 Bisimulations -}

{- A relation R on streams is a bismulation if bisimilar streams have
   the same head and their tails are related by R again. -}

record Bisim {A : Set}(_R_ : Stream A → Stream A → Set) : Set where 
  field
    hd : ∀ {as bs} → as R bs → head as ≡ head bs
    tl : ∀ {as bs} → as R bs → tail as R tail bs

open Bisim

{- We can show that ≈ is a bisimulation -}

bisim≈hd : ∀ {A} {as bs : Stream A} → as ≈ bs → head as ≡ head bs
bisim≈hd (x ∷ xs≈) = refl  

bisim≈tl : ∀ {A} {as bs : Stream A} → as ≈ bs → tail as ≈ tail bs
bisim≈tl (_ ∷ xs≈) = ♭ xs≈  

bisim≈ : ∀ {A} → Bisim (_≈_ {A})
bisim≈ = record {hd = bisim≈hd; tl = bisim≈tl}

{- On the other hand any two streams which are related by *any*
   bisimulation (which are bisimilar) are already extensionally
   equal. 
-}

bisim→≈ : {A : Set}(_R_ : Stream A → Stream A → Set) → Bisim _R_ → (as bs : Stream A) → as R bs → as ≈ bs
bisim→≈ R bisimR (a ∷ as) (b ∷ bs) asRbs with hd bisimR asRbs 
bisim→≈ R bisimR (.b ∷ as) (b ∷ bs) asRbs | refl = b ∷ (♯ bisim→≈ R bisimR (♭ as) (♭ bs) (tl bisimR asRbs))

{- Hence traditionally ≈ is defined as "the largest bisimulation". -}

{- 3 Streams are extensionally isomorphic to functions over ℕ -}

{- The function nth on streams is not partial (because there is no [])
   hence this gives rise to a function from streams to functions over
   the natural numbers.
-}
  
nthStream : ∀ {A} → Stream A → (ℕ → A)
nthStream (a ∷ as) zero = a
nthStream (a ∷ as) (suc n) = nthStream (♭ as) n

{- On the other hand given a function over the natural numbers we can
   recursively construct a corresponding stream. 
-}

mkStream : ∀ {A} → (ℕ → A) → Stream A
mkStream f = f 0 ∷ (♯ mkStream (λ n → f (suc n)))

{-
We want to show that nthStream and mkStream are inverses. However, we
have to use extensionally equality on both sides. Hence there is no
hope to be able to prove:

fun→fun : ∀ {A} → (f : ℕ → A) → nthStream (mkStream f) ≡ f
fun→fun f = {!!}

but instead:
-}

fun→fun : ∀ {A} → (f : ℕ → A) → (n : ℕ) → nthStream (mkStream f) n ≡ f n
fun→fun f zero = refl
fun→fun f (suc n) = fun→fun (λ n → f (suc n)) n

{- In the other direction we use extensional equality on streams. -}

stream→stream : ∀ {A} → (as : Stream A) → mkStream (nthStream as) ≈ as
stream→stream (a ∷ as) = a ∷ (♯ stream→stream (♭ as))

{- What about CoLists? Can they also be represented using functions
   over the natural numbers?-}

{- 4 Stream processors -}

{- Stream processors are a way to represent functions from stremas to
   streams. They are interesting becuase we have to use a mixed
   inductive - coinductive definition. -}

data SP (A B : Set) : Set where
  get : (A → SP A B) → SP A B
  put : B → ∞ (SP A B) → SP A B

{- The meaning of a stream processor is a function on streams -}

⟦_⟧_ : ∀ {A B} → SP A B → Stream A → Stream B
⟦ get f ⟧ (a ∷ as) = ⟦ f a ⟧ (♭ as)
⟦ put b sp ⟧  as = b ∷ (♯ ⟦ ♭ sp ⟧ as)

{- we can define the idnetity stream processor -}

id : ∀ {A} → SP A A
id = get (λ a → put a (♯ id))

idLem : ∀ {A} → (as : Stream A) → ⟦ id ⟧ as ≈ as
idLem (a ∷ as) = a ∷ (♯ idLem (♭ as))

{- and composition on stream processors -}

_>>>_ : ∀ {A B C} → (sp : SP A B) → (sp' : SP B C) → SP A C
get f >>> sp = get (λ a → f a >>> sp)
put b sp >>> get g = ♭ sp >>> g b
put b sp >>> put c sp' = put c (♯ put b sp >>> ♭ sp')

>>>Lem : ∀ {A B C} → (sp : SP A B) → (sp' : SP B C) → (as : Stream A) 
       → ⟦ sp >>> sp' ⟧ as ≈ ⟦ sp' ⟧ (⟦ sp ⟧ as)
>>>Lem (get f) sp (a ∷ as) = >>>Lem (f a) sp (♭ as)
>>>Lem (put b sp) (get g) as = >>>Lem (♭ sp) (g b) as
>>>Lem (put b sp) (put c sp') as = c ∷ (♯ (>>>Lem (put b sp) (♭ sp') as))

