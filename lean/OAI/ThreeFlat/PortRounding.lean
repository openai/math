import OAI.ThreeFlat.PortCatalogue
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

namespace OAI
/-! # Rounding internal demands to parallel edges in a cloud

At cloud width `W`, replace an edge of width `x` by the least number of
units whose total normalized width reaches `m * x`. Each unit can be
implemented with a binary word of length `W ⌈/⌉ m`.
-/

namespace ThreeFlat

open scoped BigOperators

/-- Normalized integer multiplicity of a bundle of width `x`. -/
def portDemandUnits (m W x : ℕ) : ℕ := (m * x) ⌈/⌉ W

@[simp] theorem portDemandUnits_zero (m W : ℕ) : portDemandUnits m W 0 = 0 := by
  simp [portDemandUnits]

/-- A single pair of cloud vertices uses at most `3 * m` units. -/
theorem portDemandUnits_le {m W x : ℕ} (hx : x ≤ 3 * W) :
    portDemandUnits m W x ≤ 3 * m := by
  obtain rfl | hW := Nat.eq_zero_or_pos W
  · simp [portDemandUnits]
  apply (ceilDiv_le_iff_le_mul hW).mpr
  calc
    m * x ≤ m * (3 * W) := Nat.mul_le_mul_left m hx
    _ = W * (3 * m) := by ring

/-- Rounding a row or column adds at most one unit per possible endpoint. -/
theorem portDemandUnits_sum_le_of_budget {m W C : ℕ} (xs : Fin m → ℕ)
    (bound : ∑ j, xs j ≤ C * W) :
    ∑ j, portDemandUnits m W (xs j) ≤ (C + 1) * m := by
  obtain rfl | hW := Nat.eq_zero_or_pos W
  · simp [portDemandUnits]
  have each (j : Fin m) : W * portDemandUnits m W (xs j) ≤ m * xs j + W := by
    unfold portDemandUnits
    rw [Nat.ceilDiv_eq_add_pred_div, Nat.mul_comm W]
    exact (Nat.div_mul_le_self _ W).trans (Nat.sub_le _ _)
  refine Nat.le_of_mul_le_mul_left ?_ hW
  calc
    W * ∑ j, portDemandUnits m W (xs j) = ∑ j, W * portDemandUnits m W (xs j) :=
      Finset.mul_sum ..
    _ ≤ ∑ j, (m * xs j + W) := Finset.sum_le_sum fun j _ => each j
    _ = m * (∑ j, xs j) + m * W := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ ≤ m * (C * W) + m * W := Nat.add_le_add_right (Nat.mul_le_mul_left m bound) _
    _ = W * ((C + 1) * m) := by ring

/-- The refresh budget of three cloud widths gives a bound of four units per slot. -/
theorem portDemandUnits_sum_le {m W : ℕ} (xs : Fin m → ℕ)
    (bound : ∑ j, xs j ≤ 3 * W) : ∑ j, portDemandUnits m W (xs j) ≤ 4 * m :=
  portDemandUnits_sum_le_of_budget xs bound

/-- Each normalized unit carries `W ⌈/⌉ m` bits, covering all of the
original demand even when the scaled widths have remainders. -/
theorem portDemandUnits_covers {m W x : ℕ} (hm : 0 < m) (hx : x ≤ 3 * W) :
    x ≤ (W ⌈/⌉ m) * portDemandUnits m W x := by
  obtain rfl | hW := Nat.eq_zero_or_pos W
  · simpa using hx
  have h₁ : m * x ≤ W * portDemandUnits m W x :=
    (ceilDiv_le_iff_le_mul hW).mp le_rfl
  have h₂ : W ≤ m * (W ⌈/⌉ m) := (ceilDiv_le_iff_le_mul hm).mp le_rfl
  refine Nat.le_of_mul_le_mul_left ?_ hm
  calc
    m * x ≤ W * portDemandUnits m W x := h₁
    _ ≤ (m * (W ⌈/⌉ m)) * portDemandUnits m W x := Nat.mul_le_mul_right _ h₂
    _ = m * ((W ⌈/⌉ m) * portDemandUnits m W x) := Nat.mul_assoc ..

private theorem width_le_row {m W : ℕ} (w : Fin m → Fin m → ℕ)
    (rows : ∀ i, ∑ j, w i j ≤ 3 * W) (i j : Fin m) : w i j ≤ 3 * W :=
  (Finset.single_le_sum (f := w i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans (rows i)

/-- The same finite catalogue of multiplicities works for every cloud width. -/
def roundedPortDemand {m : ℕ} (w : Fin m → Fin m → ℕ) (W : ℕ)
    (rows : ∀ i, ∑ j, w i j ≤ 3 * W) (cols : ∀ j, ∑ i, w i j ≤ 3 * W) :
    BoundedPortDemand m :=
  BoundedPortDemand.encode (fun i j => portDemandUnits m W (w i j))
    (fun i j => portDemandUnits_le (width_le_row w rows i j))
    (fun i => portDemandUnits_sum_le (w i) (rows i))
    (fun j => portDemandUnits_sum_le (fun i => w i j) (cols j))

@[simp] theorem roundedPortDemand_val {m : ℕ} (w : Fin m → Fin m → ℕ) (W : ℕ)
    (rows : ∀ i, ∑ j, w i j ≤ 3 * W) (cols : ∀ j, ∑ i, w i j ≤ 3 * W) (i j : Fin m) :
    ((roundedPortDemand w W rows cols).val i j).val = portDemandUnits m W (w i j) := rfl

theorem roundedPortDemand_covers {m : ℕ} (w : Fin m → Fin m → ℕ) (W : ℕ)
    (rows : ∀ i, ∑ j, w i j ≤ 3 * W) (cols : ∀ j, ∑ i, w i j ≤ 3 * W) (i j : Fin m) :
    w i j ≤ (W ⌈/⌉ m) * ((roundedPortDemand w W rows cols).val i j).val :=
  portDemandUnits_covers (Nat.zero_lt_of_lt i.isLt) (width_le_row w rows i j)

end ThreeFlat

end OAI
