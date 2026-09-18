import Mathlib

/--
Let $G$ be a group, for $g\in G$, we set $f_g(x):=gxg^{-1}$ to be an isomorphism in
$\operatorname{Aut}(G)$, prove that the kernel of the homomorphism map
$\phi:G\to\operatorname{Aut}(G),\ g\mapsto f_g$ is the center of $G$, that is
$\operatorname{Ker}\phi=Z(G)$.
-/
theorem conj_ker_eq_center (G : Type*) [Group G] :
    MonoidHom.ker (@MulAut.conj G _) = Subgroup.center G := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h y
    have hy : (MulAut.conj x) y = y := by
      rw [h]
      simp
    have hy' : x * y * x⁻¹ = y := by
      simpa [MulAut.conj_apply] using hy
    calc
      y * x = (x * y * x⁻¹) * x := by rw [hy']
      _ = x * y := by group
  · intro h
    ext y
    simp [MulAut.conj_apply]
    rw [← h y]
    group