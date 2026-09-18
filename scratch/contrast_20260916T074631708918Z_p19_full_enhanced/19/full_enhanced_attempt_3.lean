import Mathlib

/--
For positive integer $n\ge 2$, show that the ring $\mathbb Z/n\mathbb Z$ is a field if and only if
$n$ is a prime number.
-/
theorem ZMod.isField_iff_prime (n : ℕ) : IsField (ZMod n) ↔ Nat.Prime n := by
  constructor
  · intro h
    have hn_ne_zero : n ≠ 0 := by
      intro hn
      subst hn
      have h2_ne_zero : (2 : ZMod 0) ≠ 0 := by
        rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
        intro h
        have : 2 = 0 := Nat.eq_zero_of_zero_dvd h
        norm_num at this
      have h2_unit : IsUnit (2 : ZMod 0) :=
        isUnit_iff_exists_inv.mpr ⟨h.inv 2, h.mul_inv_cancel h2_ne_zero⟩
      have h2_not_unit : ¬ IsUnit (2 : ZMod 0) := by
        rw [ZMod.coe_int_isUnit_iff_isCoprime (2 : ℤ) 0]
        rw [isCoprime_zero_left, Int.isUnit_iff]
        norm_num
      exact h2_not_unit h2_unit
    have hn_ne_one : n ≠ 1 := by
      intro hn
      subst hn
      have h01 : (0 : ZMod 1) ≠ 1 := zero_ne_one
      have : (0 : ZMod 1) = 1 := (ZMod.natCast_self 1).symm
      exact h01 this
    have h2n : 2 ≤ n := by
      have h1 : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn_ne_zero, hn_ne_one⟩
      exact Nat.succ_le_of_lt h1
    rw [Nat.prime_def_lt]
    constructor
    · exact h2n
    · intro m hm_lt hm_dvd
      by_contra hm_ne_one
      have hm_pos : 0 < m := by
        by_contra hm0
        have : m = 0 := Nat.eq_zero_of_not_pos hm0
        subst this
        have : n = 0 := Nat.eq_zero_of_zero_dvd hm_dvd
        linarith
      have hm_gt1 : 1 < m :=
        Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ne_of_gt hm_pos, hm_ne_one⟩
      obtain ⟨p, hp_prime, hp_dvd_m⟩ := Nat.exists_prime_and_dvd (ne_of_gt hm_gt1)
      have hp_dvd_n : p ∣ n := dvd_trans hp_dvd_m hm_dvd
      have hp_lt_n : p < n := lt_of_le_of_lt (Nat.le_of_dvd (Nat.prime.pos hp_prime) hp_dvd_m) hm_lt
      have hp_not_unit : ¬ IsUnit (p : ZMod n) := fun hu =>
        (ZMod.isUnit_prime_iff_not_dvd hp_prime).mp hu hp_dvd_n
      have hp_ne_zero : (p : ZMod n) ≠ 0 := by
        rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
        intro hpn
        have : n ≤ p := Nat.le_of_dvd (Nat.prime.pos hp_prime) hpn
        linarith
      have hp_unit : IsUnit (p : ZMod n) :=
        isUnit_iff_exists_inv.mpr ⟨h.inv p, h.mul_inv_cancel hp_ne_zero⟩
      exact hp_not_unit hp_unit
  · intro h
    haveI : Fact n.Prime := ⟨h⟩
    infer_instance