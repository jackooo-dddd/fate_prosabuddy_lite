import Mathlib

/--
Suppose $R$ is an integral domain, show that for two element $r_1,r_2\in R$, the principal ideals $r_1R=r_2R$ iff there exists $u\in R^\times$ s.t. $r_1=ur_2$.
-/
theorem Ideal.span_eq_iff_associated {R : Type*} [CommRing R] [IsDomain R] (r₁ r₂ : R) :
    Ideal.span {r₁} = Ideal.span {r₂} ↔ ∃ u : R, IsUnit u ∧ r₁ = u * r₂ := by
  rw [Ideal.span_singleton_eq_span_singleton]
  constructor
  · intro h
    rcases (associated_iff_eq_unit_mul.mp h) with ⟨u, hu⟩
    exact ⟨(u : R), ⟨u, rfl⟩, hu⟩
  · rintro ⟨u, hu, h⟩
    rcases hu with ⟨v, hv⟩
    exact associated_iff_eq_unit_mul.mpr ⟨v, by simpa [hv] using h⟩