import Mathlib

/--
Let $R$ be a ring with identity $1$ and $x$ be an element not equal to zero. If there exists
$y \in R$ s.t. $xy = 1$ and $z \in R$ s.t. $zx = 1$, then $y=z$.
-/
theorem left_right_inverse_eq {R : Type*} [Ring R] {x y z : R} (hx : x ≠ 0) (hy : x * y = 1)
    (hz : z * x = 1) : y = z := by
  calc
    y = 1 * y := by rw [one_mul]
    _ = (z * x) * y := by rw [hz]
    _ = z * (x * y) := by rw [mul_assoc]
    _ = z * 1 := by rw [hy]
    _ = z := by rw [mul_one]
