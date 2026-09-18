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
        rcases h1 with ⟨c, hc⟩
        rw [hr2, zero_mul] at hc
        exact hc
      refine ⟨1, isUnit_one, ?_⟩
      rw [hr1, hr2]
      simp
    · rcases h1 with ⟨a, ha⟩
      rcases h2 with ⟨b, hb⟩
      have hr1 : r₁ ≠ 0 := by
        intro h0
        have : r₂ = 0 := by
          calc
            r₂ = r₁ * b := hb
            _ = 0 := by rw [h0, zero_mul]
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
    rcases hu with ⟨v, hv⟩
    rw [← hv]
    apply le_antisymm
    · rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Ideal.mem_span_singleton.mpr ⟨(v : R), mul_comm (v : R) r₂⟩
    · rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      refine Ideal.mem_span_singleton.mpr ⟨((v⁻¹ : Rˣ) : R), ?_⟩
      have hv_mul : (v : R) * ((v⁻¹ : Rˣ) : R) = 1 := by
        simp
      calc
        r₂ = r₂ * 1 := by rw [mul_one]
        _ = r₂ * ((v : R) * ((v⁻¹ : Rˣ) : R)) := by rw [hv_mul]
        _ = ((v : R) * r₂) * ((v⁻¹ : Rˣ) : R) := by ring