import Mathlib

/--
In a field $F$, for $a\in F^\times, b\in F$, the equation $ax+b=0$ has a unique solution.
-/
theorem existUnique_linear_solution {F : Type*} [Field F] {a : Fˣ} {b : F} :
    ∃! x, a * x + b = 0 := by
  refine ⟨-b * ↑a⁻¹, ?_, ?_⟩
  · calc
      ↑a * (-b * ↑a⁻¹) + b = -(↑a * (b * ↑a⁻¹)) + b := by ring
      _ = -(b * (↑a * ↑a⁻¹)) + b := by ring
      _ = -(b * 1) + b := by rw [Units.mul_inv]
      _ = 0 := by ring
  · intro y hy
    have h : ↑a * y = -b := add_eq_zero_iff_eq_neg.mp hy
    calc
      y = (↑a⁻¹ * ↑a) * y := by rw [Units.inv_mul, one_mul]
      _ = ↑a⁻¹ * (↑a * y) := by rw [mul_assoc]
      _ = ↑a⁻¹ * (-b) := by rw [h]
      _ = -b * ↑a⁻¹ := by ring