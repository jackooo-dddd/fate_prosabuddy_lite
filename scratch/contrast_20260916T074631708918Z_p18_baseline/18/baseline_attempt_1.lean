import Mathlib

/--
Let $R$ be a commutative ring with identity and $I_1$ and $I_2$ be two ideals of $R$.
Assume that $I$ is an ideal containing $I_1$ and $I_2$, prove that $I$ contains $I_1+I_2$.
-/
theorem Ideal.add_le_of_le {R : Type*} [CommRing R] (I : Ideal R) (J : Ideal R) (K : Ideal R)
    (h₁ : I ≤ K) (h₂ : J ≤ K) : I + J ≤ K := by
  intro x hx
  rw [Ideal.mem_add] at hx
  rcases hx with ⟨i, hi, j, hj, rfl⟩
  exact K.add_mem (h₁ hi) (h₂ hj)