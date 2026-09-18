import Mathlib

/--
Suppose $R$ is an integral domain, show that for two element $r_1,r_2\in R$, the principal ideals $r_1R=r_2R$ iff there exists $u\in R^\times$ s.t. $r_1=ur_2$.
-/
theorem Ideal.span_eq_iff_associated {R : Type*} [CommRing R] [IsDomain R] (r₁ r₂ : R) :
    Ideal.span {r₁} = Ideal.span {r₂} ↔ ∃ u : R, IsUnit u ∧ r₁ = u * r₂ := by
  constructor
  · intro h
    have h1 : r₂ ∣ r₁ := by
      have hmem : r₁ ∈ Ideal.span ({r₂} : Set R) := by
        rw [← h]
        exact Ideal.mem_span_singleton.mpr (dvd_refl r₁)
      exact Ideal.mem_span_singleton.mp hmem
    have h2 : r₁ ∣ r₂ := by
      have hmem : r₂ ∈ Ideal.span ({r₁} : Set R) := by
        rw [h]
        exact Ideal.mem_span_singleton.mpr (dvd_refl r₂)
      exact Ideal.mem_span_singleton.mp hmem
    by_cases hr2 : r₂ = 0
    · have hr1 : r₁ = 0 := by
        rw [hr2] at h1
        rcases h1 with ⟨c, hc⟩
        simpa using hc
      refine ⟨1, isUnit_one, ?_⟩
      rw [hr1, hr2]
      simp
    · rcases h1 with ⟨a, ha⟩
      rcases h2 with ⟨b, hb⟩
      have hr1 : r₁ ≠ 0 := by
        intro hzero
        have : r₂ = 0 := by
          calc
            r₂ = r₁ * b := hb
            _ = 0 := by rw [hzero, zero_mul]
        exact hr2 this
      have h_eq : r₁ = r₁ * (a * b) := by
        calc
          r₁ = r₂ * a := ha
          _ = (r₁ * b) * a := by rw [hb]
          _ = r₁ * (a * b) := by ring
      have hab : a * b = 1 := by
        have hmul : r₁ * (a * b) = r₁ * 1 := by
          rw [mul_one]
          exact h_eq.symm
        exact mul_left_cancel₀ hr1 hmul
      have hau : IsUnit a :=
        ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, rfl⟩
      refine ⟨a, hau, ?_⟩
      calc
        r₁ = r₂ * a := ha
        _ = a * r₂ := by rw [mul_comm]
  · rintro ⟨u, hu, heq⟩
    rw [heq]
    refine le_antisymm ?_ ?_
    · rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Ideal.mem_span_singleton.mpr ⟨u, mul_comm u r₂⟩
    · rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      rcases hu with ⟨v, hv⟩
      exact Ideal.mem_span_singleton.mpr ⟨(v⁻¹ : R), by
        calc
          r₂ = (↑v * ↑v⁻¹) * r₂ := by rw [v.mul_inv, one_mul]
          _ = (↑v * r₂) * ↑v⁻¹ := by ring
          _ = (u * r₂) * ↑v⁻¹ := by rw [hv]
      ⟩