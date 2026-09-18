import Mathlib

/--
Set $f:G\to H$ is a homomorphism between two groups.
If $f(a)$ is not of finite order, then $a$ is also not of finite order.
-/
theorem orderOf_eq_zero_of_monoidHom {G H : Type*} [Group G] [Group H] {f : G →* H} {a : G}
    (h : orderOf (f a) = 0) : orderOf a = 0 := by
  have hpow : a ^ orderOf a = 1 := pow_orderOf_eq_one a
  have hfpow : (f a) ^ orderOf a = 1 := by
    simpa only [map_pow, map_one] using congrArg f hpow
  have hdvd : orderOf (f a) ∣ orderOf a := (orderOf_dvd_iff_pow_eq_one).2 hfpow
  rw [h] at hdvd
  rcases hdvd with ⟨k, hk⟩
  simpa using hk