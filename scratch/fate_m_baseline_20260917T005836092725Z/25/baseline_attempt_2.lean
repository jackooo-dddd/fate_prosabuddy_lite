import Mathlib

/--
Let $R$ be a commutative ring with identity, and let $P_1, \dots, P_m$ be prime ideals of $R$.
If $A$ is an ideal of $R$ such that
\[ A \subseteq P_1 \cup \cdots \cup P_m, \]
then there exists some $i$ ($1 \leq i \leq m$) for which $A \subseteq P_i$.
-/
theorem primeAvoidance {R : Type} [CommRing R] (A : Ideal R) (m : ℕ)
    (P : Fin (m + 1) → Ideal R)
    (pp : ∀ i : Fin (m + 1), (P i).IsPrime)
    (hA : A.carrier ⊆ ⋃ (i : Fin (m + 1)), P i) :
    ∃ i : Fin (m + 1), A.carrier ⊆ P i := by
  classical
  have h : (A : Set R) ⊆ ⋃ i ∈ (Finset.univ : Finset (Fin (m + 1))), (P i : Set R) := by
    intro x hx
    simpa using hA hx
  obtain ⟨i, -, hi⟩ :=
    (Ideal.subset_union_prime (Finset.univ : Finset (Fin (m + 1))) P
      (by intro i _; exact pp i) A).mp h
  exact ⟨i, fun x hx => hi hx⟩