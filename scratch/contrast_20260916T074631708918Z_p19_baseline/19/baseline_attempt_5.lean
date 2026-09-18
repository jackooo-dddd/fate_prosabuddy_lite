import Mathlib

/--
For positive integer $n\ge 2$, show that the ring $\mathbb Z/n\mathbb Z$ is a field if and only if
$n$ is a prime number.
-/
theorem ZMod.isField_iff_prime (n : ℕ) : IsField (ZMod n) ↔ Nat.Prime n := by
  constructor
  · intro hf
    have hn0 : n ≠ 0 := by
      intro hn
      subst hn
      have h2 : (2 : ZMod 0) ≠ 0 := by
        rw [ZMod.natCast_zmod_eq_zero_iff_dvd 2]
        simp
      rcases hf.mul_inv_cancel h2 with ⟨c, hc⟩
      rcases ZMod.intCast_surjective 0 c with ⟨k, hk⟩
      have h' : (2 : ZMod 0) * (k : ZMod 0) = 1 := by
        rw [← hk]
        exact hc
      have h_int : (((2 : ℤ) * k : ℤ) : ZMod 0) = ((1 : ℤ) : ZMod 0) := by
        push_cast
        exact h'
      have hdiv : (0 : ℤ) ∣ ((2 : ℤ) * k - 1) :=
        (ZMod.intCast_eq_intCast_iff ((2 : ℤ) * k) 1 0).mp h_int
      rcases hdiv with ⟨d, hd⟩
      rw [zero_mul] at hd
      omega
    have hn1 : n ≠ 1 := by
      intro hn1
      haveI : Subsingleton (ZMod n) := (ZMod.subsingleton_iff n).mpr hn1
      rcases hf.exists_pair_ne with ⟨x, y, hxy⟩
      exact hxy (Subsingleton.elim x y)
    have hn_ge_two : 2 ≤ n := by omega
    rw [Nat.prime_def_lt]
    refine ⟨hn_ge_two, ?_⟩
    intro m hm_lt hm_dvd
    by_contra hm_ne_one
    rcases hm_dvd with ⟨k, hk⟩
    have hm_ne_zero : m ≠ 0 := by
      intro hm0
      have hk' : n = 0 := by simpa [hm0] using hk
      exact hn0 hk'
    have hk_ne_zero : k ≠ 0 := by
      intro hk0
      have hk' : n = 0 := by simpa [hk0] using hk
      exact hn0 hk'
    have hm_gt_one : 1 < m := by omega
    have hk_lt : k < n := by
      rw [hk]
      have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne_zero
      have : k * 1 < k * m := mul_lt_mul_of_pos_left hm_gt_one hk_pos
      simpa [mul_comm] using this
    have hm_cast_ne_zero : (m : ZMod n) ≠ 0 := by
      intro hmz
      have hdiv : n ∣ m := (ZMod.natCast_zmod_eq_zero_iff_dvd m).mp hmz
      have hm_zero : m = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hm_lt
      exact hm_ne_zero hm_zero
    have hk_cast_ne_zero : (k : ZMod n) ≠ 0 := by
      intro hkz
      have hdiv : n ∣ k := (ZMod.natCast_zmod_eq_zero_iff_dvd k).mp hkz
      have hk_zero : k = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hk_lt
      exact hk_ne_zero hk_zero
    have hmk_zero : (m : ZMod n) * (k : ZMod n) = 0 := by
      rw [← Nat.cast_mul, ← hk, ZMod.natCast_self]
    have no_zero_divisors : ∀ {a b : ZMod n}, a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by
      intro a b ha hb hab
      rcases hf.mul_inv_cancel ha with ⟨c, hc⟩
      have hc' : c * a = 1 := by rw [mul_comm c a, hc]
      have : b = 0 := by
        calc
          b = 1 * b := by rw [one_mul]
          _ = (c * a) * b := by rw [← hc']
          _ = c * (a * b) := by rw [mul_assoc]
          _ = c * 0 := by rw [hab]
          _ = 0 := by rw [mul_zero]
      exact hb this
    exact (no_zero_divisors hm_cast_ne_zero hk_cast_ne_zero) hmk_zero
  · intro hn
    letI : Fact (Nat.Prime n) := ⟨hn⟩
    infer_instance