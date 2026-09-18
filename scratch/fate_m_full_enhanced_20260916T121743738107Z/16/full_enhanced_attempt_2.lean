import Mathlib

/--
Suppose $R$ is an integral domain, show that for two element $r_1,r_2\in R$, the principal ideals $r_1R=r_2R$ iff there exists $u\in R^\times$ s.t. $r_1=ur_2$.
-/
theorem Ideal.span_eq_iff_associated {R : Type*} [CommRing R] [IsDomain R] (r₁ r₂ : R) :
    Ideal.span {r₁} = Ideal.span {r₂} ↔ ∃ u : R, IsUnit u ∧ r₁ = u * r₂ := by
  constructor
  · intro h
    have h21 : r₂ ∣ r₁ := by
      rw [← Ideal.mem_span_singleton]
      rw [← h]
      exact Ideal.mem_span_singleton.mpr dvd_rfl
    have h12 : r₁ ∣ r₂ := by
      rw [← Ideal.mem_span_singleton]
      rw [h]
      exact Ideal.mem_span_singleton.mpr dvd_rfl
    by_cases hr2 : r₂ = 0
    · subst r₂
      rcases h21 with ⟨c, hc⟩
      refine ⟨1, isUnit_one, ?_⟩
      simpa using hc
    · rcases h21 with ⟨c, hc⟩
      rcases h12 with ⟨d, hd⟩
      have h_eq : r₂ = r₂ * (c * d) := by
        calc
          r₂ = r₁ * d := hd
          _ = (r₂ * c) * d := by rw [hc]
          _ = r₂ * (c * d) := by ring
      have hzero : r₂ * (1 - c * d) = 0 := by
        calc
          r₂ * (1 - c * d) = r₂ - r₂ * (c * d) := by ring
          _ = r₂ - r₂ := by rw [← h_eq]
          _ = 0 := by ring
      have hcd : c * d = 1 := by
        rcases (mul_eq_zero.mp hzero) with h | h
        · exact False.elim (hr2 h)
        · exact (sub_eq_zero.mp h).symm
      refine ⟨c, ?_, ?_⟩
      · exact isUnit_iff_exists_inv.mpr ⟨d, hcd⟩
      · simpa [mul_comm] using hc
  · rintro ⟨u, hu, h⟩
    apply le_antisymm
    · rw [Ideal.span_singleton_le_iff_mem (Ideal.span {r₂}), Ideal.mem_span_singleton]
      exact ⟨u, by rw [h, mul_comm]⟩
    · rcases hu with ⟨v, hv⟩
      rw [← hv] at h
      rw [Ideal.span_singleton_le_iff_mem (Ideal.span {r₁}), Ideal.mem_span_singleton]
      refine ⟨↑(v⁻¹), ?_⟩
      calc
        r₂ = 1 * r₂ := by ring
        _ = (↑v * ↑(v⁻¹)) * r₂ := by rw [Units.mul_inv]
        _ = (↑v * r₂) * ↑(v⁻¹) := by ring
        _ = r₁ * ↑(v⁻¹) := by rw [← h]