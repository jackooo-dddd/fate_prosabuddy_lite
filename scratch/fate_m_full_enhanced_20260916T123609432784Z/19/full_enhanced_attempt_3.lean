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
    · have hn0 : n ≠ 0 := by
        rintro rfl
        letI : IsField (ZMod 0) := h
        have h2ne : (2 : ZMod 0) ≠ 0 := by
          rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
          norm_num
        have h2unit : IsUnit (2 : ZMod 0) := (IsField.isUnit_iff_ne_zero).mpr h2ne
        have h2not : ¬ IsUnit (2 : ZMod 0) := by
          rw [ZMod.isUnit_prime_iff_not_dvd (n := 0) (p := 2) (by norm_num)]
          simp
        exact h2not h2unit
      have hn1 : n ≠ 1 := by
        rintro rfl
        rcases h.exists_pair_ne with ⟨x, y, hxy⟩
        exact hxy (Subsingleton.elim x y)
      omega
    · rintro ⟨m, k, hm_lt, hk_lt, hmk⟩
      letI : IsField (ZMod n) := h
      have hnpos : 0 < n := by omega
      have hm0 : m ≠ 0 := by
        intro hm0
        rw [hm0, zero_mul] at hmk
        omega
      have hk0 : k ≠ 0 := by
        intro hk0
        rw [hk0, mul_zero] at hmk
        omega
      have hm1 : m ≠ 1 := by
        intro hm1
        rw [hm1, one_mul] at hmk
        omega
      have hk1 : k ≠ 1 := by
        intro hk1
        rw [hk1, mul_one] at hmk
        omega
      have hm_ge : 2 ≤ m := by omega
      have hm_dvd : m ∣ n := ⟨k, hmk.symm⟩
      have hnotcop : ¬ Nat.Coprime m n := by
        intro hcop
        have hdiv_gcd : m ∣ Nat.gcd m n := Nat.dvd_gcd (dvd_refl m) hm_dvd
        change Nat.gcd m n = 1 at hcop
        rw [hcop] at hdiv_gcd
        have hm_eq_one : m = 1 := Nat.dvd_one.mp hdiv_gcd
        omega
      have hm_ne : (m : ZMod n) ≠ 0 := by
        rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
        intro hdiv
        have hle : n ≤ m := Nat.le_of_dvd (by omega : 0 < m) hdiv
        omega
      have hmunit : IsUnit (m : ZMod n) := (IsField.isUnit_iff_ne_zero).mpr hm_ne
      have hcop : Nat.Coprime m n := (ZMod.isUnit_iff_coprime m n).mp hmunit
      exact hnotcop hcop
  · intro hn
    letI : Fact n.Prime := ⟨hn⟩
    infer_instance