import OAI.Computability.VPVNP.ShiftedBlocks
import OAI.Computability.VPVNP.CrossingCard
import Mathlib.Data.Fintype.EquivFin

/-!
# Integral factorizations for the two-wire crossing tensor

The wire labels are numbered from zero, and each of the two summands has its
own number of factor coordinates. The four integer arrays can be reduced into
any field without changing either cut.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Crossing

open Filter
open scoped BigOperators Topology

/-- Two integral matrix factorizations, one on each of the two cuts of the
product of the two identity wires. -/
structure IntegralCrossing (x y plus minus : ℕ) where
  /-- The integer factor indexed by the first operator index `i` and output state `α` on the
  forward cut. -/
  leftPlus : Fin plus → Fin x → Fin y → ℤ
  /-- The integer factor indexed by the second operator index `j` and input state `β` on the
  forward cut. -/
  rightPlus : Fin plus → Fin x → Fin y → ℤ
  /-- The integer factor indexed by the first operator index `i` and input state `β` on the
  reversed cut. -/
  leftMinus : Fin minus → Fin x → Fin y → ℤ
  /-- The integer factor indexed by the second operator index `j` and output state `α` on the
  reversed cut. -/
  rightMinus : Fin minus → Fin x → Fin y → ℤ
  identity : ∀ i j α β,
    ∑ k, leftPlus k i α * rightPlus k j β + ∑ k, leftMinus k i β * rightMinus k j α =
      (if i = j then 1 else 0) * (if α = β then 1 else 0)

private noncomputable def padded {K X Y : Type*} [Fintype K] (r : ℕ)
    (f : K → X → Y → ℤ) (k : Fin r) (x : X) (y : Y) : ℤ :=
  if h : k.val < Fintype.card K then f ((Fintype.equivFin K).symm ⟨k.val, h⟩) x y else 0

private theorem padded_contraction {K X Y : Type*} [Fintype K] {r : ℕ}
    (hr : Fintype.card K ≤ r) (f g : K → X → Y → ℤ) (i j : X) (α β : Y) :
    ∑ k, padded r f k i α * padded r g k j β = ∑ k, f k i α * g k j β := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [Fin.sum_trunc (hf := fun k => by simp [padded, Fin.natAdd])]
  simpa [padded] using (Fintype.equivFin K).symm.sum_comp (fun k => f k i α * g k j β)

/-- Convert the state and factor indices of an integral crossing to numbered
wires, padding each cut independently to its prescribed bound. -/
theorem integralCrossing_of_factors {X Y K L : Type*}
    [Fintype X] [Fintype Y] [Fintype K] [Fintype L] [DecidableEq X] [DecidableEq Y]
    {x y plus minus : ℕ} (hx : Fintype.card X = x) (hy : Fintype.card Y = y)
    (hk : Fintype.card K ≤ plus) (hl : Fintype.card L ≤ minus)
    (a b : K → X → Y → ℤ) (c d : L → X → Y → ℤ)
    (h : ∀ i j α β, ∑ k, a k i α * b k j β + ∑ k, c k i β * d k j α =
      (if i = j then 1 else 0) * (if α = β then 1 else 0)) :
    Nonempty (IntegralCrossing x y plus minus) := by
  let ex := (Fintype.equivFinOfCardEq hx).symm
  let ey := (Fintype.equivFinOfCardEq hy).symm
  refine ⟨⟨fun k i α => padded _ a k (ex i) (ey α),
    fun k j β => padded _ b k (ex j) (ey β), fun k i β => padded _ c k (ex i) (ey β),
    fun k j α => padded _ d k (ex j) (ey α), ?_⟩⟩
  intro i j α β
  rw [padded_contraction hk, padded_contraction hl, h]
  simp

/-- The same four integer factors give a decomposition of the two identity
wires over every field with the indicated flattening rank bounds. The first
tensor is flattened on `(i,α)|(j,β)` and the second on `(i,β)|(j,α)`. -/
theorem IntegralCrossing.flatteningRanks {x y plus minus : ℕ}
    (f : IntegralCrossing x y plus minus) (R : Type*) [Field R] :
    ∃ P M : Matrix (Fin x × Fin y) (Fin x × Fin y) R,
      P.rank ≤ plus ∧ M.rank ≤ minus ∧ ∀ i j α β,
        P (i,α) (j,β) + M (i,β) (j,α) =
          (if i = j then 1 else 0) * (if α = β then 1 else 0) := by
  let P : Matrix (Fin x × Fin y) (Fin x × Fin y) R :=
    fun a b => (↑(∑ k, f.leftPlus k a.1 a.2 * f.rightPlus k b.1 b.2) : R)
  let M : Matrix (Fin x × Fin y) (Fin x × Fin y) R :=
    fun a b => (↑(∑ k, f.leftMinus k a.1 a.2 * f.rightMinus k b.1 b.2) : R)
  refine ⟨P, M, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using
      factorization_rank (R := R) (fun k (p : Fin x × Fin y) => f.leftPlus k p.1 p.2)
        (fun k (p : Fin x × Fin y) => f.rightPlus k p.1 p.2)
  · simpa only [Fintype.card_fin] using
      factorization_rank (R := R) (fun k (p : Fin x × Fin y) => f.leftMinus k p.1 p.2)
        (fun k (p : Fin x × Fin y) => f.rightMinus k p.1 p.2)
  · intro i j α β
    dsimp only [P, M]
    rw [← Int.cast_add, f.identity]
    simp only [Int.cast_mul, apply_ite Int.cast, Int.cast_one, Int.cast_zero]


/-- Finite, integer form of the shifted crossing in doubled energy units.
The first wire omits the empty state, and the intermediate cutoffs differ by
twice the Laurent coefficient shift. -/
theorem integral_shifted_crossing (H E : ℕ) (s : ℤ) :
    Nonempty (IntegralCrossing (cutoffCount H - 1) (cutoffCount E)
      ((H+1)^4 * cutoffCount ((E : ℤ) + H + 2*s).toNat)
      ((H+1)^4 * cutoffCount ((E : ℤ) + H - 2*s).toNat)) := by
  let B := (2*(-s-1)).natAbs
  let N := E + B + H + 4
  have hs : |2*(-s-1)| ≤ (B : ℤ) := by simp [B]
  obtain ⟨a, b, c, d, hid⟩ := finiteShiftedCrossing N B H E s (by dsimp [N]; omega)
    (by dsimp [N]; omega) hs
  have bound (v : ℤ) : Fintype.card (BlockCoordinates H H (CrossingCutoff N v)) ≤
      (H+1)^4 * cutoffCount v.toNat := by
    apply (blockCoordinates_card_le H H (CrossingCutoff N v)).trans
    apply Nat.mul_le_mul _ (modeCutoff_card_le N v)
    calc
      H * (H+1)^3 ≤ (H+1) * (H+1)^3 := Nat.mul_le_mul_right _ (by omega)
      _ = (H+1)^4 := by ring
  exact integralCrossing_of_factors (crossingState_card H) (modeCutoff_card_eq N E (by dsimp [N]; omega))
    (bound _) (bound _) a b c d hid

/-- Theorem 3.1 of *VP and VNP differ over every field*. For two prescribed
wire rates and one signed shift, the same integer tensors work over every field.
The limits of the two factor bounds are distinct when the shift is nonzero.
The ordinary flattening ranks follow from `IntegralCrossing.flatteningRanks`. -/
theorem shiftedCrossing (t u δ : ℝ) (ht : 0 < t) (hu : 0 < u)
    (hlo : -(t^2+u^2) < δ) (hhi : δ < t^2+u^2) :
    ∃ x y plus minus : ℕ → ℕ,
      Tendsto (fun n : ℕ => Real.logb 2 (x n) / n) atTop (𝓝 t) ∧
      Tendsto (fun n : ℕ => Real.logb 2 (y n) / n) atTop (𝓝 u) ∧
      Tendsto (fun n : ℕ => Real.logb 2 (plus n) / n) atTop (𝓝 (Real.sqrt (t^2+u^2+δ))) ∧
      Tendsto (fun n : ℕ => Real.logb 2 (minus n) / n) atTop (𝓝 (Real.sqrt (t^2+u^2-δ))) ∧
      ∀ n, Nonempty (IntegralCrossing (x n) (y n) (plus n) (minus n)) := by
  obtain ⟨hx, hy, hr⟩ := shiftedCrossing_rates t u δ ht hu hlo hhi
  refine ⟨_, _, crossingFactorBound t u δ true, crossingFactorBound t u δ false,
    hx, hy, hr true, hr false, ?_⟩
  intro n
  simpa only [crossingFactorBound, Bool.false_eq_true, ↓reduceIte, add_comm
    (crossingEnergy t n : ℤ) (crossingEnergy u n : ℤ)] using
      integral_shifted_crossing (crossingEnergy t n) (crossingEnergy u n) (crossingShift δ n)

end Crossing

end VPVNP
end Computability
end OAI
