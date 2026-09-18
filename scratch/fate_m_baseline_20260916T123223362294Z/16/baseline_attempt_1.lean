import Mathlib

/--
Suppose $R$ is an integral domain, show that for two element $r_1,r_2\in R$, the principal ideals $r_1R=r_2R$ iff there exists $u\in R^\times$ s.t. $r_1=ur_2$.
-/
theorem Ideal.span_eq_iff_associated {R : Type*} [CommRing R] [IsDomain R] (r₁ r₂ : R) :
    Ideal.span {r₁} = Ideal.span {r₂} ↔ ∃ u : R, IsUnit u ∧ r₁ = u * r₂ := by
  constructor
  · intro h
    have h12 : r₂ ∣ r₁ := by
      have : r₁ ∈ Ideal.span {r₂} := by
        rw [← h]
        exact Ideal.subset_span (by simp)
      simpa [Ideal.mem_span_singleton] using this
    have h21 : r₁ ∣ r₂ := by
      have : r₂ ∈ Ideal.span {r₁} := by
        rw [h]
        exact Ideal.subset_span (by simp)
      simpa [Ideal.mem_span_singleton] using this
    rcases h12 with ⟨a, ha⟩
    rcases h21 with ⟨b, hb⟩
    by_cases h₁ : r₁ = 0
    · have h₂ : r₂ = 0 := by simpa [h₁] using hb
      refine ⟨1, isUnit_one, ?_⟩
      rw [h₁, h₂]
      simp
    · have h_eq : r₁ * (b * a) = r₁ * 1 := by
        rw [mul_one]
        calc
          r₁ * (b * a) = (r₁ * b) * a := by ring
          _ = r₂ * a := by rw [← hb]
          _ = r₁ := by rw [← ha]
      have hba : b * a = 1 := mul_left_cancel₀ h₁ h_eq
      have ha_unit : IsUnit a := by
        rw [isUnit_iff_exists_inv]
        exact ⟨b, by rw [mul_comm, hba]⟩
      exact ⟨a, ha_unit, by simpa [mul_comm] using ha⟩
  · rintro ⟨u, hu, h⟩
    rw [h]
    exact Ideal.span_singleton_mul_left_unit hu r₂