import Mathlib

/--
In a field $F$, as a ring, it has only ideals $(0)=\{0\},(1)=F$.
-/
theorem Field.ideal_eq_bot_or_top {F : Type*} [Field F] (I : Ideal F) : I = 0 ∨ I = ⊤ := by
  by_cases h : I = ⊥
  · exact Or.inl h
  · right
    have hnot : ¬ ∀ x ∈ I, x = 0 := by
      intro hall
      exact h ((Ideal.eq_bot_iff I).2 hall)
    push_neg at hnot
    obtain ⟨x, hxI, hx0⟩ := hnot
    have h1 : (1 : F) ∈ I := by
      have hxinv : x⁻¹ * x ∈ I := I.mul_mem_left x⁻¹ hxI
      simpa [inv_mul_cancel₀ hx0] using hxinv
    exact (Ideal.eq_top_iff_one I).2 h1