import Mathlib

/--
Suppose $R$ is an integral domain, show that for two element $r_1,r_2\in R$, the principal ideals $r_1R=r_2R$ iff there exists $u\in R^\times$ s.t. $r_1=ur_2$.
-/
theorem Ideal.span_eq_iff_associated {R : Type*} [CommRing R] [IsDomain R] (r₁ r₂ : R) :
    Ideal.span {r₁} = Ideal.span {r₂} ↔ ∃ u : R, IsUnit u ∧ r₁ = u * r₂ := by
  constructor
  · intro h
    have hmem₁ : r₁ ∈ Ideal.span {r₂} := by
      rw [← h]
      exact Ideal.subset_span (by simp)
    have hmem₂ : r₂ ∈ Ideal.span {r₁} := by
      rw [h]
      exact Ideal.subset_span (by simp)
    by_cases hr₂ : r₂ = 0
    · have hr₁ : r₁ = 0 := by
        rw [hr₂] at hmem₁
        rw [Ideal.mem_span_singleton] at hmem₁
        rcases hmem₁ with ⟨c, hc⟩
        simpa using hc
      refine ⟨1, isUnit_one, ?_⟩
      rw [hr₁, hr₂]
      simp
    · rw [Ideal.mem_span_singleton] at hmem₁ hmem₂
      rcases hmem₁ with ⟨c, hc⟩
      rcases hmem₂ with ⟨d, hd⟩
      have hcd : c * d = 1 := by
        apply mul_left_cancel₀ hr₂
        calc
          r₂ * (c * d) = (r₂ * c) * d := by ring
          _ = r₁ * d := by rw [← hc]
          _ = r₂ := by rw [← hd]
          _ = r₂ * 1 := by rw [mul_one]
      have hcunit : IsUnit c := by
        refine ⟨⟨c, d, hcd, ?_⟩, rfl⟩
        rw [mul_comm, hcd]
      refine ⟨c, hcunit, ?_⟩
      calc
        r₁ = r₂ * c := hc
        _ = c * r₂ := by rw [mul_comm]
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨v, hv⟩ := hu
    rw [← hv]
    have hvv : (↑v : R) * ↑v⁻¹ = 1 := by
      rw [← Units.val_mul, Units.mul_inv, Units.val_one]
    apply le_antisymm
    · rw [Ideal.span_singleton_le_iff_mem]
      rw [Ideal.mem_span_singleton]
      exact ⟨↑v, by rw [mul_comm]⟩
    · rw [Ideal.span_singleton_le_iff_mem]
      rw [Ideal.mem_span_singleton]
      refine ⟨↑v⁻¹, ?_⟩
      calc
        r₂ = (↑v * ↑v⁻¹) * r₂ := by rw [hvv, one_mul]
        _ = (↑v * r₂) * ↑v⁻¹ := by ring