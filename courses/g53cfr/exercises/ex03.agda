{- 
  Computer Aided Formal Reasoning (G53CFR, G54CFR)
  Thorsten Altenkirch

  Exercise 3: Propositional Logic (12/2/09)
  Deadline: 19/2/09, 12:00

  Use the coursework submission (id: 264)) system to submit the coursework
  after demonstrating it in the lab to me or Darin.
  
  Prove the following propositions of propositional logic by
  completing the sheds { .. }. You may add parameters and use pattern
  matching. You are also welcome to prove auxilliary propositions.

  Make sure that the files from the last two lectures (l05.agda and
  l06.agda) are in the same directory because we are importing them.

  Note that not all propositions may be provable. If you think that a
  proposition is unprovable clearly mark this one by adding a line:
  -- impossible.

-}

module ex03 where

open import l05
open import l06

B : {P Q R : Prp} → (P ⇒ Q) ⇒ (Q ⇒ R) ⇒ P ⇒ R
B = ?

C : {P Q R : Prp} → (P ⇒ Q ⇒ R) ⇒ Q ⇒ P ⇒ R
C = ?

fst : {P Q : Prp} → P ∧ Q ⇒ P
fst = ?

snd : {P Q : Prp} → P ∧ Q ⇒ Q
snd = ?

curry-1 : {P Q R : Prp} → (P ∧ Q ⇒ R) ⇒ P ⇒ Q ⇒ R
curry-1 = ?

curry-2 : {P Q R : Prp} → (P ⇒ Q ⇒ R) ⇒ P ∧ Q ⇒ R
curry-2 = ?

curry : {P Q R : Prp} → (P ∧ Q ⇒ R) ⇔ (P ⇒ Q ⇒ R)
curry = ?

oradj-1 : {P Q R : Prp} → (P ∨ Q ⇒ R) ⇒ ((P ⇒ R) ∧ (Q ⇒ R))
oradj-1 = ?

oradj-2 : {P Q R : Prp} → ((P ⇒ R) ∧ (Q ⇒ R)) ⇒ (P ∨ Q ⇒ R)
oradj-2 = ?

oradj : {P Q R : Prp} → (P ∨ Q ⇒ R) ⇔ ((P ⇒ R) ∧ (Q ⇒ R))
oradj = ?

pierce : {P Q : Prp} → ((P ⇒ Q) ⇒ P) ⇒ P
pierce = ?

TND→RND : TND → RAA
TND→RND = ?

¬¬deMorgan¬∧ : {P Q : Prp} → ¬ (P ∧ Q) ⇒ ¬¬ ((¬ P) ∨ (¬ Q))
¬¬deMorgan¬∧ = ?

ret¬¬ : {P : Prp} → P ⇒ ¬¬ P
ret¬¬ = ?

bind¬¬ : {P Q : Prp} → ¬¬ P ⇒ (P ⇒ ¬¬ Q) ⇒ ¬¬ Q 
bind¬¬ = ?

map¬¬ : {P Q : Prp} → ¬¬ P ⇒ (P ⇒ Q) ⇒ ¬¬ Q
map¬¬ = ?

app¬¬ : {P Q : Prp} → ¬¬ (P ⇒ Q) ⇒ ¬¬ P ⇒ ¬¬ Q
app¬¬ = ?

∧¬¬-1 : {P Q : Prp} → ¬¬ (P ∧ Q) ⇒ ¬¬ P ∧ ¬¬ Q
∧¬¬-1 = ?

∧¬¬-2 : {P Q : Prp} → ¬¬ P ∧ ¬¬ Q ⇒ ¬¬ (P ∧ Q) 
∧¬¬-2 = ?

∧¬¬ : {P Q : Prp} → ¬¬ (P ∧ Q) ⇔ ¬¬ P ∧ ¬¬ Q
∧¬¬ = ?

∨¬¬-1 : {P Q : Prp} → ¬¬ (P ∨ Q) ⇒ ¬¬ P ∨ ¬¬ Q
∨¬¬-1 = ?

∨¬¬-2 : {P Q : Prp} → ¬¬ P ∨ ¬¬ Q ⇒ ¬¬ (P ∨ Q) 
∨¬¬-2 = ?

∨¬¬ : {P Q : Prp} → ¬¬ (P ∨ Q) ⇔ ¬¬ P ∨ ¬¬ Q
∨¬¬ = ?

