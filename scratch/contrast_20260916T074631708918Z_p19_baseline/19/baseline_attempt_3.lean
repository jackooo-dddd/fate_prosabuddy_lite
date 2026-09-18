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
        rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
        norm_num
      have h : (2 : ZMod 0) * (2 : ZMod 0)⁻¹ = 1 := hf.mul_inv_cancel h2
      rcases ZMod.intCast_surjective 0 (2 : ZMod 0)⁻¹ with ⟨k, hk⟩
      have h' : (2 : ZMod 0) * (k : ZMod 0) = 1 := by
        simpa [hk] using h
      have h_int : (((2 : ℤ) * k : ℤ) : ZMod 0) = ((1 : ℤ) : ZMod 0) := by
        push_cast
        exact h'
      have hdiv : (0 : ℤ) ∣ ((2 : ℤ) * k - 1) :=
        (ZMod.intCast_eq_intCast_iff ((2 : ℤ) * k) 1 0).mp h_int
      rcases hdiv with ⟨c, hc⟩
      rw [zero_mul] at hc
      omega
    have hne_one : n ≠ 1 := by
      intro hn1
      haveI : Subsingleton (ZMod n) := (ZMod.subsingleton_iff).mpr hn1
      rcases hf.exists_pair_ne with ⟨x, y, hxy⟩
      exact hxy (Subsingleton.elim x y)
    have hn_ge_two : 2 ≤ n := by omega
    refine ⟨hn_ge_two, ?_⟩
    intro m hm
    by_cases hm1 : m = 1
    · exact Or.inl hm1
    · right
      by_contra hmn
      rcases hm with ⟨k, hk⟩
      have hm_ne_zero : (m : ZMod n) ≠ 0 := by
        intro hmz
        have hdiv : n ∣ m := (ZMod.natCast_zmod_eq_zero_iff_dvd m n).mp hmz
        have hmn' : m ∣ n := ⟨k, hk⟩
        have hmn_eq : m = n := Nat.dvd_antisymm hmn' hdiv
        exact hmn hmn_eq
      have hk_ne_zero : (k : ZMod n) ≠ 0 := by
        intro hkz
        have hdiv : n ∣ k := (ZMod.natCast_zmod_eq_zero_iff_dvd k n).mp hkz
        have hkn : k ∣ n := ⟨m, by rw [hk, mul_comm]⟩
        have hkn_eq : k = n := Nat.dvd_antisymm hkn hdiv
        have hm_eq_one : m = 1 := by
          have hn_eq : n = m * n := by
            calc
              n = m * k := hk
              _ = m * n := by rw [hkn_eq]
          have h1 : 1 * n = m * n := by
            rw [one_mul]
            exact hn_eq
          exact (Nat.mul_right_cancel h1 hn0).symm
        exact hm1 hm_eq_one
      have hmk : (m : ZMod n) * (k : ZMod n) = 0 := by
        rw [← Nat.cast_mul, ← hk, ZMod.natCast_self]
      have mul_ne_zero : ∀ {a b : ZMod n}, a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by
        intro a b ha hb hab
        have hb0 : b = 0 := by
          calc
            b = 1 * b := by rw [one_mul]
            _ = (a * a⁻¹) * b := by rw [hf.mul_inv_cancel ha]
            _ = (a⁻¹ * a) * b := by rw [mul_comm a (a⁻¹)]
            _ = a⁻¹ * (a * b) := by rw [mul_assoc]
            _ = a⁻¹ * 0 := by rw [hab]
            _ = 0 := by rw [mul_zero]
        exact hb hb0
      exact (mul_ne_zero hm_ne_zero hk_ne_zero) hmk
  · intro hn
    letI : Fact (Nat.Prime n) := ⟨hn⟩
    infer_instance