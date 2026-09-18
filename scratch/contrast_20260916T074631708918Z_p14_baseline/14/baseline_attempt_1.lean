import Mathlib

/--
In an integral domain $R$, if $a\in R$ and natural number $n\in\mathbb N$ satisfy $a^n=0$,
then $a=0$.
-/
theorem zero_of_pow_eq_zero {R : Type*} [Ring R] [IsDomain R] (a : R) (n : ℕ)
    (eq : a ^ n = 0) : a = 0 := by
  induction n with
  | zero =>
      rw [pow_zero] at eq
      exact (one_ne_zero eq).elim
  | succ n ih =>
      rw [pow_succ] at eq
      rcases (mul_eq_zero.mp eq) with h | h
      · exact ih h
      · exact h