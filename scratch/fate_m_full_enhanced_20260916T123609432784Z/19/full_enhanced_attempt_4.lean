import Mathlib

/--
For positive integer $n\ge 2$, show that the ring $\mathbb Z/n\mathbb Z$ is a field if and only if
$n$ is a prime number.
-/
theorem ZMod.isField_iff_prime (n : ℕ) : IsField (ZMod n) ↔ Nat.Prime n := by
  constructor
  · intro h
    have h2n : 2 ≤ n := by
      by_contra hlt
      push_neg at hlt
      interval_cases n
      · have h2 : (2 : ZMod 0) ≠ 0 := by
          rw [ZMod.natCast_eq_zero_iff_dvd]
          norm_num
        have hunit : IsUnit (2 : ZMod 0) := by
          rw [isUnit_iff_exists_inv']
          exact ⟨h.inv 2, h.mul_inv_cancel (2 : ZMod 0) h2⟩
        have hnot : ¬ IsUnit (2 : ZMod 0) := by
          rw [ZMod.isUnit_iff_coprime]
          norm_num
        exact hnot hunit
      · obtain ⟨x, y, hxy⟩ := h.exists_pair_ne
        have : Subsingleton (ZMod 1) := inferInstance
        exact hxy (Subsingleton.elim x y)
    rw [Nat.prime_iff_not_exists_mul_eq]
    constructor
    · exact h2n
    · rintro ⟨a, b, ha, hb, hab⟩
      have ha0 : a ≠ 0 := by
        intro ha0
        subst ha0
        simp at hab
        omega
      have hb0 : b ≠ 0 := by
        intro hb0
        subst hb0
        simp at hab
        omega
      have ha_ne : (a : ZMod n) ≠ 0 := by
        rw [ZMod.natCast_eq_zero_iff_dvd]
        intro hdiv
        have : a = 0 := Nat.eq_zero_of_dvd_of_lt hdiv ha
        exact ha0 this
      have hb_ne : (b : ZMod n) ≠ 0 := by
        rw [ZMod.natCast_eq_zero_iff_dvd]
        intro hdiv
        have : b = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hb
        exact hb0 this
      have hmul : (a : ZMod n) * (b : ZMod n) = 0 := by
        rw [← Nat.cast_mul, hab, ZMod.natCast_self]
      haveI : IsField (ZMod n) := h
      have hzero : (a : ZMod n) = 0 ∨ (b : ZMod n) = 0 := mul_eq_zero.mp hmul
      cases hzero with
      | inl ha_zero => exact ha_ne ha_zero
      | inr hb_zero => exact hb_ne hb_zero
  · intro hp
    haveI : Fact (Nat.Prime n) := ⟨hp⟩
    infer_instance