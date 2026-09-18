import Mathlib

/--
For positive integer $n\ge 2$, show that the ring $\mathbb Z/n\mathbb Z$ is a field if and only if
$n$ is a prime number.
-/
theorem ZMod.isField_iff_prime (n : ℕ) : IsField (ZMod n) ↔ Nat.Prime n := by
  constructor
  · intro h
    have hn0 : n ≠ 0 := by
      intro hn
      subst hn
      have h2 : (2 : ZMod 0) ≠ 0 := by norm_num
      rcases h.mul_inv_cancel 2 h2 with ⟨b, hb⟩
      have hunit : IsUnit (2 : ZMod 0) := isUnit_iff_exists_inv.mpr ⟨b, hb⟩
      rw [ZMod.isUnit_iff_coprime] at hunit
      exact (by norm_num : ¬ 2.Coprime 0) hunit
    have hn1 : n ≠ 1 := by
      intro hn
      subst hn
      haveI : Subsingleton (ZMod 1) := (ZMod.subsingleton_iff 1).mpr rfl
      rcases h.exists_pair_ne with ⟨x, y, hxy⟩
      exact hxy (Subsingleton.elim x y)
    have hn2 : 2 ≤ n := by omega
    rw [Nat.prime_def_lt]
    constructor
    · exact hn2
    · intro m hm_lt hm_dvd
      by_contra hm_ne1
      have hm_pos : 0 < m := Nat.pos_of_dvd_of_pos hm_dvd (by omega)
      have hm_gt1 : 1 < m := by omega
      have hm_ne_zero : (m : ZMod n) ≠ 0 := by
        rw [ZMod.natCast_eq_zero_iff_dvd]
        intro hd
        have : n ≤ m := Nat.le_of_dvd hm_pos hd
        omega
      rcases h.mul_inv_cancel m hm_ne_zero with ⟨b, hb⟩
      have hunit : IsUnit (m : ZMod n) := isUnit_iff_exists_inv.mpr ⟨b, hb⟩
      rw [ZMod.isUnit_iff_coprime] at hunit
      have hgcd : Nat.gcd m n = m := Nat.gcd_eq_left hm_dvd
      rw [hgcd] at hunit
      omega
  · intro hn
    haveI : Fact n.Prime := ⟨hn⟩
    infer_instance