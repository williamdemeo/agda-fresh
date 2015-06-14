{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Thorsten Altenkirch

  Exercise 3: Propositional Logic (12/2/09)
  Deadline: 19/2/09, 12:00

  Use the coursework submission (id: 264)) system to submit the coursework
  after demonstrating it in the lab to me or Darin.
  
  Prove the following propositions of propositional logic by
  completing the sheds { .. }.

  Note that not all propositions may be provable. If you think that a
  proposition is unprovable clearly mark this one by adding a line:
  -- impossible.

-}

module ex03 where

open import l05
open import l06

B : {P Q R : Prp} → (P ⇒ Q) ⇒ (Q ⇒ R) ⇒ P ⇒ R
B pq qr p = qr (pq p)

C : {P Q R : Prp} → (P ⇒ Q ⇒ R) ⇒ Q ⇒ P ⇒ R
C pqr q p = pqr p q

fst : {P Q : Prp} → P ∧ Q ⇒ P
fst (p , q) = p

snd : {P Q : Prp} → P ∧ Q ⇒ Q
snd (p , q) = q

curry-1 : {P Q R : Prp} → (P ∧ Q ⇒ R) ⇒ P ⇒ Q ⇒ R
curry-1 pqr p q = pqr (p , q)

curry-2 : {P Q R : Prp} → (P ⇒ Q ⇒ R) ⇒ P ∧ Q ⇒ R
curry-2 pqr (p , q) = pqr p q

curry : {P Q R : Prp} → (P ∧ Q ⇒ R) ⇔ (P ⇒ Q ⇒ R)
curry = curry-1 , curry-2

oradj-1 : {P Q R : Prp} → (P ∨ Q ⇒ R) ⇒ ((P ⇒ R) ∧ (Q ⇒ R))
oradj-1 pqr = (λ p → pqr (left p)) , λ q → pqr (right q)

oradj-2 : {P Q R : Prp} → ((P ⇒ R) ∧ (Q ⇒ R)) ⇒ (P ∨ Q ⇒ R)
oradj-2 (pr , qr) (left p) = pr p
oradj-2 (pr , qr) (right q) = qr q

oradj : {P Q R : Prp} → (P ∨ Q ⇒ R) ⇔ ((P ⇒ R) ∧ (Q ⇒ R))
oradj = oradj-1 , oradj-2

pierce : {P Q : Prp} → ((P ⇒ Q) ⇒ P) ⇒ P
pierce pqp = pqp (λ p → {!!}) --impossible

TND→RND : TND → RAA
TND→RND tnd {P} nnp with tnd {P}
TND→RND tnd nnp | left p = p
TND→RND tnd nnp | right np = efq (nnp np)

¬¬deMorgan¬∧ : {P Q : Prp} → ¬ (P ∧ Q) ⇒ ¬¬ ((¬ P) ∨ (¬ Q))
¬¬deMorgan¬∧ npq nnpnq = nnpnq (left (λ p → 
             nnpnq (right (λ q → npq (p , q)))))

ret¬¬ : {P : Prp} → P ⇒ ¬¬ P
ret¬¬ p np = np p 

bind¬¬ : {P Q : Prp} → ¬¬ P ⇒ (P ⇒ ¬¬ Q) ⇒ ¬¬ Q 
bind¬¬ nnp pnnq nq = nnp (λ p → pnnq p nq)

map¬¬ : {P Q : Prp} → ¬¬ P ⇒ (P ⇒ Q) ⇒ ¬¬ Q
map¬¬ np pq = bind¬¬ np (λ p → ret¬¬ (pq p))

app¬¬ : {P Q : Prp} → ¬¬ (P ⇒ Q) ⇒ ¬¬ P ⇒ ¬¬ Q
app¬¬ nnpq nnp = bind¬¬ nnpq (λ pq → bind¬¬ nnp (λ p → ret¬¬ (pq p)))

∧¬¬-1 : {P Q : Prp} → ¬¬ (P ∧ Q) ⇒ ¬¬ P ∧ ¬¬ Q
∧¬¬-1 nnpq = map¬¬ nnpq fst , map¬¬ nnpq snd

∧¬¬-2 : {P Q : Prp} → ¬¬ P ∧ ¬¬ Q ⇒ ¬¬ (P ∧ Q) 
∧¬¬-2 (nnp , nnq) = bind¬¬ nnp (λ p → map¬¬ nnq  (λ q → p , q))

∧¬¬ : {P Q : Prp} → ¬¬ (P ∧ Q) ⇔ ¬¬ P ∧ ¬¬ Q
∧¬¬ = ∧¬¬-1 , ∧¬¬-2

∨¬¬-1 : {P Q : Prp} → ¬¬ (P ∨ Q) ⇒ ¬¬ P ∨ ¬¬ Q
∨¬¬-1 nnpq = {!!} --impossible

∨¬¬-2 : {P Q : Prp} → ¬¬ P ∨ ¬¬ Q ⇒ ¬¬ (P ∨ Q) 
∨¬¬-2 (left np) = map¬¬ np left
∨¬¬-2 (right nq) = map¬¬ nq right

∨¬¬ : {P Q : Prp} → ¬¬ (P ∨ Q) ⇔ ¬¬ P ∨ ¬¬ Q
∨¬¬ = {!!} --impossible

