import Mathlib

/--
Prove that a if $G$ and $H$ are finite groups and their orders are coprime,
then any homomorphism $f: G \rightarrow H$ is trivial, i.e. $f(G) = \{ 1_H \}$.
-/
theorem MonoidHom.eq_id_of_card_gcd_eq_one {G H: Type*} [Finite H] [Finite G][Group G] [Group H]
    (h : (Nat.card H).gcd (Nat.card G) = 1) (f : G →* H) : ∀ p : G , f p = 1 := by
  intro p
  have hH : orderOf (f p) ∣ Nat.card H := orderOf_dvd_natCard (f p)
  have hmap : orderOf (f p) ∣ orderOf p := by
    rw [orderOf_dvd_iff_pow_eq_one]
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hG : orderOf (f p) ∣ Nat.card G := dvd_trans hmap (orderOf_dvd_natCard p)
  have hgcd : orderOf (f p) ∣ (Nat.card H).gcd (Nat.card G) := Nat.dvd_gcd hH hG
  rw [h] at hgcd
  have hone : orderOf (f p) = 1 := Nat.dvd_one.mp hgcd
  exact orderOf_eq_one_iff.mp hone