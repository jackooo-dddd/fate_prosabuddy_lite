import Mathlib

/--
For positive integer $n\ge 2$, show that the ring $\mathbb Z/n\mathbb Z$ is a field if and only if
$n$ is a prime number.
-/
theorem ZMod.isField_iff_prime (n : ℕ) : IsField (ZMod n) ↔ Nat.Prime n := by
  constructor
  case mp =>
    intro h
    by_contra hn
    have hunit_of_ne_zero : ∀ {a : ZMod n}, a ≠ 0 → IsUnit a := by
      intro a ha
      refine ⟨⟨a, h.inv a, h.mul_inv_cancel ha, ?_⟩, rfl⟩
      rw [mul_comm]
      exact h.mul_inv_cancel ha
    have h0 : n ≠ 0 := by
      intro hn0
      have hp : Nat.Prime 2 := by norm_num
      have hnotunit : ¬ IsUnit ((2 : ℕ) : ZMod n) := by
        intro hunit
        have : ¬ 2 ∣ n := (ZMod.isUnit_prime_iff_not_dvd hp).mp hunit
        rw [hn0] at this
        exact this (dvd_zero 2)
      have hne : ((2 : ℕ) : ZMod n) ≠ 0 := by
        rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
        rw [hn0]
        norm_num
      exact hnotunit (hunit_of_ne_zero hne)
    have h01 : (0 : ZMod n) ≠ 1 := by
      intro h01
      obtain ⟨x, y, hxy⟩ := h.exists_pair_ne
      apply hxy
      have h10 : (1 : ZMod n) = 0 := h01.symm
      calc
        x = x * 1 := by rw [mul_one]
        _ = x * 0 := by rw [h10]
        _ = 0 := by simp
        _ = y * 0 := by simp
        _ = y * 1 := by rw [← h10]
        _ = y := by rw [mul_one]
    have h1 : n ≠ 1 := by
      intro hn1
      have hzero : (1 : ZMod n) = 0 := by
        rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
        rw [hn1]
        norm_num
      exact h01 hzero.symm
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd h1
    have hp_lt_n : p < n := by
      have hp_le_n : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hpdvd
      have hp_ne_n : p ≠ n := by
        intro hpn
        rw [hpn] at hp
        exact hn hp
      exact lt_of_le_of_ne hp_le_n hp_ne_n
    have hne : (p : ZMod n) ≠ 0 := by
      rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
      intro hndvd
      have : n ≤ p := Nat.le_of_dvd hp.pos hndvd
      exact not_lt_of_ge this hp_lt_n
    have hnotunit : ¬ IsUnit ((p : ℕ) : ZMod n) := by
      intro hunit
      have : ¬ p ∣ n := (ZMod.isUnit_prime_iff_not_dvd hp).mp hunit
      exact this hpdvd
    exact hnotunit (hunit_of_ne_zero hne)
  case mpr =>
    intro hn
    haveI : Fact n.Prime := ⟨hn⟩
    infer_instance