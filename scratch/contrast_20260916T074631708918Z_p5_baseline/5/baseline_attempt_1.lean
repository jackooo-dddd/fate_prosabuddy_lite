import Mathlib

/--
Prove that a homomorphism $\phi: G \rightarrow G^{\prime}$ is an isomorphism
(There exists a two-sided inverse map $\phi^{-1}:G'\to G$)
if and only if it is injective and surjective.
-/
theorem has_inverse_iff_isomorphism {G G' : Type*} [Group G] [Group G'] (φ : G →* G') :
    (∃ φ₁ : G' → G, Function.LeftInverse φ₁ φ ∧ Function.RightInverse φ₁ φ) ↔
    (Function.Injective φ ∧ Function.Surjective φ) := by
  constructor
  · rintro ⟨φ₁, hleft, hright⟩
    constructor
    · intro x y hxy
      calc
        x = φ₁ (φ x) := (hleft x).symm
        _ = φ₁ (φ y) := by rw [hxy]
        _ = y := hleft y
    · intro y
      exact ⟨φ₁ y, hright y⟩
  · rintro ⟨hinj, hsurj⟩
    classical
    let φ₁ : G' → G := fun y => Classical.choose (hsurj y)
    have hright : Function.RightInverse φ₁ φ := fun y => Classical.choose_spec (hsurj y)
    have hleft : Function.LeftInverse φ₁ φ := by
      intro x
      apply hinj
      exact hright (φ x)
    exact ⟨φ₁, hleft, hright⟩