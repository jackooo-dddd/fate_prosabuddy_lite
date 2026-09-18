import Mathlib

/--
For positive integer $n\ge 2$, show that the ring $\mathbb Z/n\mathbb Z$ is a field if and only if
$n$ is a prime number.
-/
theorem ZMod.isField_iff_prime (n : ℕ) : IsField (ZMod n) ↔ Nat.Prime n := by
  constructor
  · intro h
    have hn0 : n ≠ 0 := by
      rintro rfl
      have h2 : (2 : ZMod 0) ≠ 0 := by
        rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
        exact (by decide : ¬ 0 ∣ 2)
      have hunit : IsUnit (2 : ZMod 0) := (IsField.isUnit_iff_ne_zero).mpr h2
      rw [ZMod.isUnit_iff_coprime] at hunit
      exact (by decide : ¬ Nat.Coprime 2 0) hunit
    have hn1 : n ≠ 1 := by
      rintro rfl
      obtain ⟨x, y, hxy⟩ := h.exists_pair_ne
      exact hxy (Subsingleton.elim x y)
    have hn2 : 2 ≤ n := by omega
    rw [Nat.prime_def_lt]
    refine ⟨hn2, ?_⟩
    intro m hm_lt hm_dvd
    by_contra hm1
    have hm_ne_zero : (m : ZMod n) ≠ 0 := by
      intro hzero
      rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at hzero
      have hm_eq_zero : m = 0 := Nat.eq_zero_of_dvd_of_lt hzero hm_lt
      subst hm_eq_zero
      have : n = 0 := by
        rcases hm_dvd with ⟨c, hc⟩
        rw [zero_mul] at hc
        exact hc
      omega
    have hunit : IsUnit (m : ZMod n) := (IsField.isUnit_iff_ne_zero).mpr hm_ne_zero
    rw [ZMod.isUnit_iff_coprime] at hunit
    rw [Nat.coprime_iff_gcd_eq_one] at hunit
    have hgcd : Nat.gcd m n = m := Nat.gcd_eq_left hm_dvd
    rw [hgcd] at hunit
    exact hm1 hunit
  · intro hn
    letI : Fact n.Prime := ⟨hn⟩
    infer_instance