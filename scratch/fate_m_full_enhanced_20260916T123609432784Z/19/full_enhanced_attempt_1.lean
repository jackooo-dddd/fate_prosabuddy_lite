import Mathlib

/--
For positive integer $n\ge 2$, show that the ring $\mathbb Z/n\mathbb Z$ is a field if and only if
$n$ is a prime number.
-/
theorem ZMod.isField_iff_prime (n : ℕ) : IsField (ZMod n) ↔ Nat.Prime n := by
  constructor
  · intro h
    have hne0 : n ≠ 0 := by
      intro hn0
      subst n
      have h2ne : (2 : ZMod 0) ≠ 0 := by
        rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
        norm_num
      have h2unit : IsUnit (2 : ZMod 0) := by
        rcases h.mul_inv_cancel h2ne with ⟨c, hc⟩
        exact isUnit_iff_exists_inv.mpr ⟨c, hc⟩
      have hcop : Nat.Coprime 2 0 := (ZMod.isUnit_iff_coprime 2).mp h2unit
      have hnot : ¬ Nat.Coprime 2 0 := by norm_num [Nat.Coprime]
      exact hnot hcop
    have hne1 : n ≠ 1 := by
      intro hn1
      subst n
      have hsub : Subsingleton (ZMod 1) := ⟨fun x y => by
        have h1 : (1 : ZMod 1) = 0 := ZMod.natCast_self 1
        have hx : x = 0 := by
          calc
            x = x * 1 := by rw [mul_one]
            _ = x * 0 := by rw [h1]
            _ = 0 := by rw [mul_zero]
        have hy : y = 0 := by
          calc
            y = y * 1 := by rw [mul_one]
            _ = y * 0 := by rw [h1]
            _ = 0 := by rw [mul_zero]
        rw [hx, hy]⟩
      rcases h.exists_pair_ne with ⟨x, y, hxy⟩
      exact hxy (hsub.allEq x y)
    have hn2 : 2 ≤ n := by omega
    have hprime : Nat.Prime n := by
      refine (Nat.prime_def_lt.mpr ?_)
      refine ⟨hn2, ?_⟩
      intro m hm_lt hdiv
      by_contra hmne
      have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hdiv (by omega : 0 < n)
      have hm1 : 1 < m := by
        exact lt_of_le_of_ne (Nat.succ_le_of_lt hmpos) (Ne.symm hmne)
      rcases hdiv with ⟨k, rfl⟩
      have hkpos : 0 < k := by
        by_contra hk
        have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
        subst k
        simp at hn2
        exact hn2
      have hk_lt : k < m * k := by
        calc
          k = 1 * k := by rw [one_mul]
          _ < m * k := Nat.mul_lt_mul_of_pos_right hm1 hkpos
      have hm_ne : (m : ZMod (m * k)) ≠ 0 := by
        rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
        intro hdiv'
        have : m * k ≤ m := Nat.le_of_dvd (by omega : 0 < m * k) hdiv'
        omega
      have hk_ne : (k : ZMod (m * k)) ≠ 0 := by
        rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
        intro hdiv'
        have : m * k ≤ k := Nat.le_of_dvd (by omega : 0 < m * k) hdiv'
        omega
      have hprod : (m : ZMod (m * k)) * (k : ZMod (m * k)) = 0 := by
        rw [← Nat.cast_mul, ZMod.natCast_self]
      have hk_zero : (k : ZMod (m * k)) = 0 := by
        rcases h.mul_inv_cancel hm_ne with ⟨c, hc⟩
        calc
          (k : ZMod (m * k)) = ((m : ZMod (m * k)) * c) * (k : ZMod (m * k)) := by
            rw [hc, one_mul]
          _ = c * ((m : ZMod (m * k)) * (k : ZMod (m * k))) := by
            rw [mul_comm (m : ZMod (m * k)) c, mul_assoc]
          _ = 0 := by
            rw [hprod, mul_zero]
      exact hk_ne hk_zero
    exact hprime
  · intro hn
    haveI : Fact n.Prime := ⟨hn⟩
    infer_instance