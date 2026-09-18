import Mathlib

/--
Set $f:G\to H$ is a homomorphism between two groups.
If the range of $f$ has $n$ elements, then $x^{n} \in \operatorname{Ker} f$ for every $x \in G$.
-/
theorem pow_mem_ker_of_card_eq {G H : Type*} [Group G] [Group H] (f : G →* H) (n : ℕ)
    (h : Nat.card f.range = n) : ∀ g : G, (g ^ n) ∈ f.ker := by
  classical
  intro g
  rw [MonoidHom.mem_ker]
  by_cases hn : n = 0
  · simp [hn]
  · have hpos : 0 < Nat.card f.range := by
      rw [h]
      exact Nat.pos_of_ne_zero hn
    haveI : Finite f.range := by
      obtain ⟨h1, h2⟩ := Nat.card_pos_iff.mp hpos
      first | exact h1 | exact h2
    haveI : Fintype f.range := Fintype.ofFinite f.range
    let x : f.range := ⟨f g, ⟨g, rfl⟩⟩
    have hcard : Fintype.card f.range = n := by
      rw [← Nat.card_eq_fintype_card]
      exact h
    have hdiv : orderOf x ∣ n := by
      rw [← hcard]
      exact orderOf_dvd_card_univ x
    have hx : x ^ n = 1 := orderOf_dvd_iff_pow_eq_one.mp hdiv
    have hval : (f g) ^ n = 1 := by
      have := congrArg (fun y : f.range => (y : H)) hx
      simpa [x] using this
    simpa [map_pow] using hval