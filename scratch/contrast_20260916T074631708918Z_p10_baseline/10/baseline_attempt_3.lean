import Mathlib

/--
Set $f:G\to H$ is a homomorphism between two groups.
If the range of $f$ has $n$ elements, then $x^{n} \in \operatorname{Ker} f$ for every $x \in G$.
-/
theorem pow_mem_ker_of_card_eq {G H : Type*} [Group G] [Group H] (f : G →* H) (n : ℕ)
    (h : Nat.card f.range = n) : ∀ g : G, (g ^ n) ∈ f.ker := by
  intro g
  rw [MonoidHom.mem_ker, map_pow]
  let x : f.range := ⟨f g, ⟨g, rfl⟩⟩
  have hdiv : orderOf x ∣ n := by
    rw [← h]
    exact orderOf_dvd_natCard x
  have hx : x ^ n = 1 := orderOf_dvd_iff_pow_eq_one.mp hdiv
  have hval : (f g) ^ n = 1 := by
    have := congrArg (fun y : f.range => (y : H)) hx
    simpa [x] using this
  exact hval