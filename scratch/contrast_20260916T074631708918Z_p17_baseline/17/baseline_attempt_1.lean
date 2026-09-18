import Mathlib

/--
Suppose that $R$ is a commutative ring with identity. For a subset $S$ of $R$,
let $\operatorname{Span}(S)$ be the minimal ideal containing elements in $S$. Prove that
$\operatorname{Span}(S)=\left\{\sum_{s\in S'}r_ss|S'\text{ is a finite subset of }S,r_s\in R\
\forall s\in S'\right\}.$
In other words, prove that the latter one is an ideal and any ideal containing $S$
also contains the right-hand-side.
-/
theorem ideal_span_eq_diagonal_map_sum {R : Type*} [CommRing R] (S : Set R) :
    (Ideal.span S) = {x : R | ∃ T : Multiset (R × S),
      x = Multiset.sum (Multiset.map (fun (x : R × S) ↦ (x.1 : R) * (x.2 : R)) T)} := by
  let f : R × S → R := fun p => p.1 * p.2
  let A : Set R := {x | ∃ T : Multiset (R × S), x = Multiset.sum (Multiset.map f T)}
  have hA_zero : (0 : R) ∈ A := by
    refine ⟨0, ?_⟩
    simp [f]
  have hA_add : ∀ {x y : R}, x ∈ A → y ∈ A → x + y ∈ A := by
    intro x y hx hy
    rcases hx with ⟨T, rfl⟩
    rcases hy with ⟨U, rfl⟩
    refine ⟨T + U, ?_⟩
    simp [Multiset.map_add, Multiset.sum_add]
  have hA_smul : ∀ (c : R) {x : R}, x ∈ A → c * x ∈ A := by
    intro c x hx
    rcases hx with ⟨T, rfl⟩
    induction T using Multiset.induction_on with
    | empty =>
        refine ⟨0, ?_⟩
        simp [f]
    | cons p T ih =>
        rw [Multiset.map_cons, Multiset.sum_cons, mul_add]
        apply hA_add
        · refine ⟨{ (c * p.1, p.2) }, ?_⟩
          simp [f, mul_assoc]
        · exact ih
  let A_sub : Submodule R R :=
  { carrier := A,
    zero_mem' := hA_zero,
    add_mem' := by
      intro x y hx hy
      exact hA_add hx hy,
    smul_mem' := by
      intro c x hx
      simpa [smul_eq_mul] using hA_smul c hx }
  let I : Ideal R :=
  { A_sub with
    mul_mem_right' := by
      intro a b hb
      simpa [smul_eq_mul, mul_comm] using A_sub.smul_mem a hb }
  have hS : S ⊆ (I : Set R) := by
    intro s hs
    change ∃ T : Multiset (R × S), s = Multiset.sum (Multiset.map f T)
    refine ⟨{ ((1 : R), ⟨s, hs⟩) }, ?_⟩
    simp [f]
  have h_span_le : (Ideal.span S : Set R) ⊆ A := by
    intro x hx
    exact (Ideal.span_le.mpr hS) hx
  have hA_le_span : A ⊆ (Ideal.span S : Set R) := by
    intro x hx
    rcases hx with ⟨T, rfl⟩
    clear hx x
    induction T using Multiset.induction_on with
    | empty =>
        simp
    | cons p T ih =>
        rw [Multiset.map_cons, Multiset.sum_cons]
        apply Ideal.add_mem
        · simpa [f] using Ideal.mul_mem_left (p.1) (Ideal.subset_span p.2.property)
        · exact ih
  exact Set.eq_of_subset_of_subset h_span_le hA_le_span
