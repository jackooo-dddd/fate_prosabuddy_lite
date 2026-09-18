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
      subst n
      haveI : IsField (ZMod 0) := h
      have h2ne : (2 : ZMod 0) ≠ 0 := by
        rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
        decide
      have hunit : IsUnit (2 : ZMod 0) := IsField.isUnit h2ne
      have hcop : Nat.Coprime 2 0 := by
        simpa [ZMod.isUnit_iff_coprime] using hunit
      have hnot : ¬ Nat.Coprime 2 0 := by decide
      exact hnot hcop
    have hn1 : n ≠ 1 := by
      intro hn
      subst n
      haveI : Subsingleton (ZMod 1) := by
        refine ⟨fun x y => ?_⟩
        have h10 : (1 : ZMod 1) = 0 := ZMod.natCast_self 1
        have h01 : (0 : ZMod 1) = 1 := h10.symm
        calc
          x = x * 1 := (mul_one x).symm
          _ = x * 0 := by rw [← h01]
          _ = 0 := mul_zero x
          _ = y * 0 := (mul_zero y).symm
          _ = y * 1 := by rw [h01]
          _ = y := mul_one y
      rcases h.exists_pair_ne with ⟨x, y, hxy⟩
      exact hxy (Subsingleton.elim x y)
    have hn2 : 2 ≤ n := by omega
    rw [Nat.prime_def_lt]
    refine ⟨hn2, ?_⟩
    intro m hmlt hmdvd
    by_contra hm1
    have hmpos : 0 < m := by
      by_contra hm0
      have hm0' : m = 0 := by omega
      subst m
      rcases hmdvd with ⟨k, hk⟩
      have hn0 : n = 0 := by simpa using hk
      omega
    have hmgt1 : 1 < m := by omega
    have hmne : (m : ZMod n) ≠ 0 := by
      rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
      intro hn_dvd_m
      have hm0 : m = 0 := Nat.eq_zero_of_dvd_of_lt hn_dvd_m hmlt
      omega
    haveI : IsField (ZMod n) := h
    have hunit : IsUnit (m : ZMod n) := IsField.isUnit hmne
    have hcop : Nat.Coprime m n := by
      simpa [ZMod.isUnit_iff_coprime] using hunit
    have hcopmm : Nat.Coprime m m := hcop.coprime_dvd_right hmdvd
    have hm_eq_one : m = 1 := Nat.coprime_self.mp hcopmm
    exact hm1 hm_eq_one
  · intro hn
    haveI : Fact (Nat.Prime n) := ⟨hn⟩
    exact inferInstance