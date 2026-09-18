import Mathlib

/--
Suppose $R$ is an integral domain, show that for two element $r_1,r_2\in R$, the principal ideals $r_1R=r_2R$ iff there exists $u\in R^\times$ s.t. $r_1=ur_2$.
-/
theorem Ideal.span_eq_iff_associated {R : Type*} [CommRing R] [IsDomain R] (r₁ r₂ : R) :
    Ideal.span {r₁} = Ideal.span {r₂} ↔ ∃ u : R, IsUnit u ∧ r₁ = u * r₂ := by
  constructor
  · intro h
    have h21 : r₂ ∣ r₁ := by
      have hmem : r₁ ∈ Ideal.span ({r₂} : Set R) := by
        rw [← h]
        exact Ideal.subset_span (by simp)
      exact Ideal.mem_span_singleton.mp hmem
    have h12 : r₁ ∣ r₂ := by
      have hmem : r₂ ∈ Ideal.span ({r₁} : Set R) := by
        rw [h]
        exact Ideal.subset_span (by simp)
      exact Ideal.mem_span_singleton.mp hmem
    have hassoc : Associated r₂ r₁ := associated_iff_dvd.mpr ⟨h21, h12⟩
    rcases hassoc with ⟨u, hu⟩
    refine ⟨(u : R), ⟨u, rfl⟩, ?_⟩
    calc
      r₁ = r₂ * (u : R) := hu
      _ = (u : R) * r₂ := mul_comm _ _
  · rintro ⟨u, hu, h_eq⟩
    apply le_antisymm
    · rw [Ideal.span_singleton_le_iff_mem]
      rw [Ideal.mem_span_singleton]
      refine ⟨u, ?_⟩
      rw [h_eq]
      exact mul_comm _ _
    · rw [Ideal.span_singleton_le_iff_mem]
      rw [Ideal.mem_span_singleton]
      rcases hu with ⟨v, rfl⟩
      refine ⟨(↑(v⁻¹) : R), ?_⟩
      have h2 : (↑(v⁻¹) : R) * r₁ = r₂ := by
        rw [h_eq]
        rw [← mul_assoc, Units.inv_mul, one_mul]
      rw [← h2]
      exact mul_comm _ _