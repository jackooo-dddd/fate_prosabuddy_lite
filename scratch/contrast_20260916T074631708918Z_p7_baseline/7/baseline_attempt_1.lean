import Mathlib

/--
Let $\phi: G \rightarrow G^{\prime}$ be a group homomorphism. Show that $\phi(G)$ is Abelian
if and only if $x y x^{-1} y^{-1} \in \operatorname{Ker}(\phi)$ for all $x, y \in G$.
-/
theorem commutative_iff_commutator_mem_ker  {G H : Type} [Group G] [Group H] (f : G →* H) :
    (∀ x y : H, x ∈ f.range ∧ y ∈ f.range → x * y = y * x)
    ↔ ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ f.ker := by
  constructor
  · intro h x y
    have hxmem : f x ∈ f.range := by
      rw [MonoidHom.mem_range]
      exact ⟨x, rfl⟩
    have hymem : f y ∈ f.range := by
      rw [MonoidHom.mem_range]
      exact ⟨y, rfl⟩
    have hxy : f x * f y = f y * f x := h (f x) (f y) ⟨hxmem, hymem⟩
    rw [MonoidHom.mem_ker]
    calc
      f (x * y * x⁻¹ * y⁻¹) = f x * f y * (f x)⁻¹ * (f y)⁻¹ := by
        simp [map_mul, map_inv]
      _ = f y * f x * (f x)⁻¹ * (f y)⁻¹ := by rw [hxy]
      _ = 1 := by group
  · intro h x y hxy
    rw [MonoidHom.mem_range] at hxy
    rcases hxy with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    rw [← ha, ← hb]
    have hc : f a * f b * (f a)⁻¹ * (f b)⁻¹ = 1 := by
      have hker : a * b * a⁻¹ * b⁻¹ ∈ f.ker := h a b
      rw [MonoidHom.mem_ker] at hker
      simpa [map_mul, map_inv] using hker
    calc
      f a * f b = (f a * f b * (f a)⁻¹ * (f b)⁻¹) * (f b * f a) := by
        group
      _ = 1 * (f b * f a) := by rw [hc]
      _ = f b * f a := by simp