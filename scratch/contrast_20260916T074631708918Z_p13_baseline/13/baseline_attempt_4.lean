import Mathlib

/--
Let $R$ be a ring, and suppose that $a^3=a, \forall a\in R$. Prove that $R$ is commutative.
-/
theorem commutative_of_relations {R : Type*} [Ring R] : (∀ a : R, a ^ 3 = a) →
    ∀ (a b : R), a * b = b * a := by
  intro h a b
  have h_plus : ∀ x y : R, x ^ 2 * y + x * y * x + x * y ^ 2 + y * x ^ 2 + y * x * y + y ^ 2 * x = 0 := by
    intro x y
    have h1 : (x + y) ^ 3 = x + y := h (x + y)
    have hx : x ^ 3 = x := h x
    have hy : y ^ 3 = y := h y
    have h_expand : (x + y) ^ 3 =
        x ^ 3 + x ^ 2 * y + x * y * x + x * y ^ 2 + y * x ^ 2 + y * x * y + y ^ 2 * x + y ^ 3 := by
      noncomm_ring
    calc
      x ^ 2 * y + x * y * x + x * y ^ 2 + y * x ^ 2 + y * x * y + y ^ 2 * x
          = (x + y) ^ 3 - (x + y) := by
            rw [h_expand]
            rw [hx, hy]
            noncomm_ring
      _ = 0 := by rw [h1]; noncomm_ring
  have h_sub : ∀ x y : R, x ^ 2 * y + x * y * x - x * y ^ 2 + y * x ^ 2 - y * x * y - y ^ 2 * x = 0 := by
    intro x y
    have hneg := h_plus x (-y)
    have h_eq : - (x ^ 2 * y + x * y * x - x * y ^ 2 + y * x ^ 2 - y * x * y - y ^ 2 * x)
        = x ^ 2 * (-y) + x * (-y) * x + x * (-y) ^ 2 + (-y) * x ^ 2 + (-y) * x * (-y) + (-y) ^ 2 * x := by
      noncomm_ring
    have h' : - (x ^ 2 * y + x * y * x - x * y ^ 2 + y * x ^ 2 - y * x * y - y ^ 2 * x) = 0 := by
      rw [h_eq]
      exact hneg
    exact neg_eq_zero.mp h'
  have hA : ∀ x : R, 3 * (x - x ^ 2) = 0 := by
    intro x
    have hx : x ^ 3 = x := h x
    have hx4 : x ^ 4 = x ^ 2 := by
      calc
        x ^ 4 = x ^ 3 * x := by noncomm_ring
        _ = x * x := by rw [hx]
        _ = x ^ 2 := by noncomm_ring
    have h1 : (x - x ^ 2) * (x - x ^ 2) = -2 * (x - x ^ 2) := by
      calc
        (x - x ^ 2) * (x - x ^ 2) = x ^ 2 - x ^ 3 - x ^ 3 + x ^ 4 := by noncomm_ring
        _ = x ^ 2 - x - x + x ^ 2 := by rw [hx, hx4]
        _ = -2 * (x - x ^ 2) := by noncomm_ring
    have h2 : (x - x ^ 2) ^ 3 = 4 * (x - x ^ 2) := by
      have hsq : (x - x ^ 2) ^ 2 = -2 * (x - x ^ 2) := by
        rw [pow_two]
        exact h1
      calc
        (x - x ^ 2) ^ 3 = (x - x ^ 2) * (x - x ^ 2) ^ 2 := by noncomm_ring
        _ = (x - x ^ 2) * (-2 * (x - x ^ 2)) := by rw [hsq]
        _ = -2 * ((x - x ^ 2) * (x - x ^ 2)) := by noncomm_ring
        _ = -2 * (-2 * (x - x ^ 2)) := by rw [h1]
        _ = 4 * (x - x ^ 2) := by noncomm_ring
    have h3 : (x - x ^ 2) ^ 3 = x - x ^ 2 := h (x - x ^ 2)
    calc
      3 * (x - x ^ 2) = 4 * (x - x ^ 2) - (x - x ^ 2) := by noncomm_ring
      _ = (x - x ^ 2) - (x - x ^ 2) := by rw [← h2, h3]
      _ = 0 := by noncomm_ring
  have hB : ∀ x : R, 3 * (x + x ^ 2) = 0 := by
    intro x
    have hx : x ^ 3 = x := h x
    have hx4 : x ^ 4 = x ^ 2 := by
      calc
        x ^ 4 = x ^ 3 * x := by noncomm_ring
        _ = x * x := by rw [hx]
        _ = x ^ 2 := by noncomm_ring
    have h1 : (x + x ^ 2) * (x + x ^ 2) = 2 * (x + x ^ 2) := by
      calc
        (x + x ^ 2) * (x + x ^ 2) = x ^ 2 + x ^ 3 + x ^ 3 + x ^ 4 := by noncomm_ring
        _ = x ^ 2 + x + x + x ^ 2 := by rw [hx, hx4]
        _ = 2 * (x + x ^ 2) := by noncomm_ring
    have h2 : (x + x ^ 2) ^ 3 = 4 * (x + x ^ 2) := by
      have hsq : (x + x ^ 2) ^ 2 = 2 * (x + x ^ 2) := by
        rw [pow_two]
        exact h1
      calc
        (x + x ^ 2) ^ 3 = (x + x ^ 2) * (x + x ^ 2) ^ 2 := by noncomm_ring
        _ = (x + x ^ 2) * (2 * (x + x ^ 2)) := by rw [hsq]
        _ = 2 * ((x + x ^ 2) * (x + x ^ 2)) := by noncomm_ring
        _ = 2 * (2 * (x + x ^ 2)) := by rw [h1]
        _ = 4 * (x + x ^ 2) := by noncomm_ring
    have h3 : (x + x ^ 2) ^ 3 = x + x ^ 2 := h (x + x ^ 2)
    calc
      3 * (x + x ^ 2) = 4 * (x + x ^ 2) - (x + x ^ 2) := by noncomm_ring
      _ = (x + x ^ 2) - (x + x ^ 2) := by rw [← h2, h3]
      _ = 0 := by noncomm_ring
  have hC : ∀ x : R, 6 * x = 0 := by
    intro x
    have h1 : 3 * (x - x ^ 2) = 0 := hA x
    have h2 : 3 * (x + x ^ 2) = 0 := hB x
    calc
      6 * x = 3 * (x - x ^ 2) + 3 * (x + x ^ 2) := by noncomm_ring
      _ = 0 + 0 := by rw [h1, h2]
      _ = 0 := by noncomm_ring
  have hD : ∀ a b : R, 3 * (a * b + b * a) = 0 := by
    intro a b
    have h1 : 3 * ((a + b) - (a + b) ^ 2) = 0 := hA (a + b)
    have h2 : 3 * (a - a ^ 2) = 0 := hA a
    have h3 : 3 * (b - b ^ 2) = 0 := hA b
    have hsum : 3 * ((a + b) - (a + b) ^ 2) - 3 * (a - a ^ 2) - 3 * (b - b ^ 2) = 0 := by
      rw [h1, h2, h3]
      noncomm_ring
    have hpoly : 3 * ((a + b) - (a + b) ^ 2) - 3 * (a - a ^ 2) - 3 * (b - b ^ 2) = -(3 * (a * b + b * a)) := by
      noncomm_ring
    have hneg : -(3 * (a * b + b * a)) = 0 := by
      rw [← hpoly]
      exact hsum
    exact neg_eq_zero.mp hneg
  have hE : ∀ x y : R, 2 * (x ^ 2 * y + x * y * x + y * x ^ 2) = 0 := by
    intro x y
    have hadd := h_plus x y
    have hsub := h_sub x y
    calc
      2 * (x ^ 2 * y + x * y * x + y * x ^ 2)
        = (x ^ 2 * y + x * y * x + x * y ^ 2 + y * x ^ 2 + y * x * y + y ^ 2 * x)
          + (x ^ 2 * y + x * y * x - x * y ^ 2 + y * x ^ 2 - y * x * y - y ^ 2 * x) := by noncomm_ring
      _ = 0 + 0 := by rw [hadd, hsub]
      _ = 0 := by noncomm_ring
  have hF : ∀ a b : R, 2 * (a * b - b * a) = 0 := by
    intro a b
    have h4 : 2 * (a * b + a ^ 2 * b * a + a * b * a ^ 2) = 0 := by
      have ha : a ^ 3 = a := h a
      have h4' := hE a (a * b)
      have h_in : a * b + a ^ 2 * b * a + a * b * a ^ 2
          = a ^ 2 * (a * b) + a * (a * b) * a + (a * b) * a ^ 2 := by
        rw [show a ^ 2 * (a * b) = a ^ 3 * b by noncomm_ring, ha]
        noncomm_ring
      rw [h_in]
      exact h4'
    have h5 : 2 * (a ^ 2 * b * a + a * b * a ^ 2 + b * a) = 0 := by
      have ha : a ^ 3 = a := h a
      have h5' := hE a (b * a)
      have h_in : a ^ 2 * b * a + a * b * a ^ 2 + b * a
          = a ^ 2 * (b * a) + a * (b * a) * a + (b * a) * a ^ 2 := by
        rw [show (b * a) * a ^ 2 = b * a ^ 3 by noncomm_ring, ha]
        noncomm_ring
      rw [h_in]
      exact h5'
    calc
      2 * (a * b - b * a)
        = 2 * (a * b + a ^ 2 * b * a + a * b * a ^ 2) - 2 * (a ^ 2 * b * a + a * b * a ^ 2 + b * a) := by noncomm_ring
      _ = 0 - 0 := by rw [h4, h5]
      _ = 0 := by noncomm_ring
  have hG : ∀ a b : R, 3 * (a * b - b * a) = 0 := by
    intro a b
    have h1 := hD a b
    have h2 := hC (b * a)
    calc
      3 * (a * b - b * a) = 3 * (a * b + b * a) - 6 * (b * a) := by noncomm_ring
      _ = 0 - 0 := by rw [h1, h2]
      _ = 0 := by noncomm_ring
  have h2 := hF a b
  have h3 := hG a b
  have hzero : a * b - b * a = 0 := by
    calc
      a * b - b * a = 3 * (a * b - b * a) - 2 * (a * b - b * a) := by noncomm_ring
      _ = 0 - 0 := by rw [h3, h2]
      _ = 0 := by noncomm_ring
  exact sub_eq_zero.mp hzero