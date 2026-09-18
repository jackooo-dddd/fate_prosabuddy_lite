import Mathlib

/--
Suppose $R$ is an integral domain, show that for two element $r_1,r_2\in R$, the principal ideals $r_1R=r_2R$ iff there exists $u\in R^\times$ s.t. $r_1=ur_2$.
-/
theorem Ideal.span_eq_iff_associated {R : Type*} [CommRing R] [IsDomain R] (r₁ r₂ : R) :
    Ideal.span {r₁} = Ideal.span {r₂} ↔ ∃ u : R, IsUnit u ∧ r₁ = u * r₂ := by
  constructor
  · intro h
    have hle1 : Ideal.span {r₁} ≤ Ideal.span {r₂} := le_of_eq h
    have hle2 : Ideal.span {r₂} ≤ Ideal.span {r₁} := le_of_eq h.symm
    have hmem1 : r₁ ∈ Ideal.span {r₂} :=
      (Ideal.span_singleton_le_iff_mem (Ideal.span {r₂})).mp hle1
    have hmem2 : r₂ ∈ Ideal.span {r₁} :=
      (Ideal.span_singleton_le_iff_mem (Ideal.span {r₁})).mp hle2
    have hdiv1 : r₂ ∣ r₁ := (Ideal.mem_span_singleton).mp hmem1
    have hdiv2 : r₁ ∣ r₂ := (Ideal.mem_span_singleton).mp hmem2
    rcases hdiv1 with ⟨c, hc⟩
    rcases hdiv2 with ⟨d, hd⟩
    by_cases hr2 : r₂ = 0
    · refine ⟨1, isUnit_one, ?_⟩
      rw [hr2, mul_zero]
      rw [hr2] at hc
      simpa using hc
    · have hmul : r₂ * (c * d) = r₂ * 1 := by
        calc
          r₂ * (c * d) = (r₂ * c) * d := by rw [mul_assoc]
          _ = r₁ * d := by rw [← hc]
          _ = r₂ := hd.symm
          _ = r₂ * 1 := by rw [mul_one]
      have hcd : c * d = 1 := mul_left_cancel₀ hr2 hmul
      let u : Rˣ := ⟨c, d, hcd, by rw [mul_comm, hcd]⟩
      refine ⟨c, ⟨u, rfl⟩, ?_⟩
      rw [hc, mul_comm]
  · rintro ⟨u, hu, hr⟩
    rcases hu with ⟨v, hv⟩
    rw [← hv] at hr
    have hdiv1 : r₂ ∣ r₁ := by
      refine ⟨↑v, ?_⟩
      rw [hr, mul_comm]
    have hdiv2 : r₁ ∣ r₂ := by
      refine ⟨↑(v⁻¹), ?_⟩
      calc
        r₂ = ↑(v⁻¹) * r₁ := by
          rw [hr]
          rw [← mul_assoc]
          rw [Units.inv_mul v, one_mul]
        _ = r₁ * ↑(v⁻¹) := by rw [mul_comm]
    have hle1 : Ideal.span {r₁} ≤ Ideal.span {r₂} :=
      (Ideal.span_singleton_le_iff_mem (Ideal.span {r₂})).mpr ((Ideal.mem_span_singleton).mpr hdiv1)
    have hle2 : Ideal.span {r₂} ≤ Ideal.span {r₁} :=
      (Ideal.span_singleton_le_iff_mem (Ideal.span {r₁})).mpr ((Ideal.mem_span_singleton).mpr hdiv2)
    exact le_antisymm hle1 hle2