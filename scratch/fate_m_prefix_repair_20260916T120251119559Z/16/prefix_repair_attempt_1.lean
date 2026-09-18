import Mathlib

/--
Suppose $R$ is an integral domain, show that for two element $r_1,r_2\in R$, the principal ideals $r_1R=r_2R$ iff there exists $u\in R^\times$ s.t. $r_1=ur_2$.
-/
theorem Ideal.span_eq_iff_associated {R : Type*} [CommRing R] [IsDomain R] (r₁ r₂ : R) :
    Ideal.span {r₁} = Ideal.span {r₂} ↔ ∃ u : R, IsUnit u ∧ r₁ = u * r₂ := by
  constructor
  · intro h
    have h₁ : r₁ ∈ Ideal.span ({r₂} : Set R) := by
      rw [← h]
      exact Ideal.mem_span_singleton_self r₁
    have h₂ : r₂ ∈ Ideal.span ({r₁} : Set R) := by
      rw [h]
      exact Ideal.mem_span_singleton_self r₂
    have hdiv₁ : r₂ ∣ r₁ := Ideal.mem_span_singleton.mp h₁
    have hdiv₂ : r₁ ∣ r₂ := Ideal.mem_span_singleton.mp h₂
    rcases hdiv₁ with ⟨a, ha⟩
    rcases hdiv₂ with ⟨b, hb⟩
    by_cases hr₁ : r₁ = 0
    · have hr₂ : r₂ = 0 := by simpa [hr₁] using hb
      refine ⟨1, isUnit_one, ?_⟩
      simp [hr₁, hr₂]
    · have h_eq : r₁ = r₁ * (b * a) := by
        calc
          r₁ = r₂ * a := ha
          _ = (r₁ * b) * a := by rw [hb]
          _ = r₁ * (b * a) := by rw [mul_assoc]
      have hba : b * a = 1 := by
        have h_cancel : r₁ * (b * a) = r₁ * 1 := by simpa using h_eq.symm
        exact mul_left_cancel₀ hr₁ h_cancel
      have ha_unit : IsUnit a := by
        exact isUnit_iff_exists_inv.mpr ⟨b, by simpa [mul_comm] using hba⟩
      refine ⟨a, ha_unit, ?_⟩
      simpa [mul_comm] using ha
  · rintro ⟨u, hu, hr⟩
    rw [hr]
    apply le_antisymm
    · rw [Ideal.span_singleton_le_span_singleton]
      exact ⟨u, by rw [mul_comm]⟩
    · rw [Ideal.span_singleton_le_span_singleton]
      rcases (isUnit_iff_exists_inv.mp hu) with ⟨v, hv⟩
      refine ⟨v, ?_⟩
      calc
        r₂ = 1 * r₂ := by rw [one_mul]
        _ = (u * v) * r₂ := by rw [hv]
        _ = u * (v * r₂) := by rw [mul_assoc]
        _ = u * (r₂ * v) := by rw [mul_comm v r₂]
        _ = (u * r₂) * v := by rw [← mul_assoc]