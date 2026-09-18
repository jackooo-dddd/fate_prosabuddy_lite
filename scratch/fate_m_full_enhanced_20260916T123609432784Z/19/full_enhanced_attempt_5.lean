import Mathlib

/--
For positive integer $n\ge 2$, show that the ring $\mathbb Z/n\mathbb Z$ is a field if and only if
$n$ is a prime number.
-/
theorem ZMod.isField_iff_prime (n : ℕ) : IsField (ZMod n) ↔ Nat.Prime n := by
  constructor
  · intro h
    rw [Nat.prime_iff_not_exists_mul_eq]
    constructor
    · by_contra hn
      have hn' : n = 0 ∨ n = 1 := by omega
      rcases hn' with rfl | rfl
      · have h2 : (2 : ZMod 0) ≠ 0 := by
          rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
          norm_num
        have hunit : IsUnit (2 : ZMod 0) :=
          isUnit_iff_exists_inv.mpr ⟨(2 : ZMod 0)⁻¹, h.mul_inv_cancel _ h2⟩
        have hcop : IsCoprime (0 : ℤ) 2 := by
          apply (ZMod.coe_int_isUnit_iff_isCoprime (2 : ℤ) 0).mp
          simpa using hunit
        rcases hcop with ⟨a, b, hab⟩
        simp at hab
        omega
      · exact h.zero_ne_one (Subsingleton.elim (0 : ZMod 1) (1 : ZMod 1))
    · rintro ⟨m, k, hm, hk, hmk⟩
      have hnpos : 0 < n := by omega
      have hm0 : (m : ZMod n) ≠ 0 := by
        rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
        intro hdvd
        have hm_eq : m = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hm
        have : n = 0 := by
          rw [← hmk, hm_eq, zero_mul]
        omega
      have hk0 : (k : ZMod n) ≠ 0 := by
        rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
        intro hdvd
        have hk_eq : k = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hk
        have : n = 0 := by
          rw [← hmk, hk_eq, mul_zero]
        omega
      have hprod : (m : ZMod n) * (k : ZMod n) = 0 := by
        rw [← Nat.cast_mul, hmk, ZMod.natCast_self]
      have hk_eq : (k : ZMod n) = 0 := by
        have hm_inv := h.mul_inv_cancel (m : ZMod n) hm0
        calc
          (k : ZMod n) = 1 * (k : ZMod n) := by rw [one_mul]
          _ = ((m : ZMod n) * (m : ZMod n)⁻¹) * (k : ZMod n) := by rw [← hm_inv]
          _ = (m : ZMod n)⁻¹ * ((m : ZMod n) * (k : ZMod n)) := by ring
          _ = (m : ZMod n)⁻¹ * 0 := by rw [hprod]
          _ = 0 := by rw [mul_zero]
      exact hk0 hk_eq
  · intro hn
    haveI : Fact (Nat.Prime n) := ⟨hn⟩
    infer_instance