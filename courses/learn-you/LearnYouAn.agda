module LearnYouAn where

  data nat : Set where
    zero : nat
    succ : nat -> nat

  _+_ : nat -> nat -> nat
  zero + n = n
  (succ n) + m = succ (n + m)

  data _even : nat -> Set where
    ZERO : zero even
    STEP : (x : nat) -> x even -> succ (succ x) even

