import OAI.Computability.VPVNP.CursorPadding
import OAI.Computability.VPVNP.SlotPacking

/-!
# Designating lane coordinates on the cursor graph

Number the bits of the site address in increasing order of significance. Any
partition of these coordinates supplies a base part and a binary vector of
lanes in the sense of Section 7. At a fixed cursor and slot, the displacement
in both parts is independent of the address. This also applies to the
zero-width parallel copies of the no-flip arc.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorNetwork

open CursorRouting
open Compression (BitWord SlotGraph LiftedSlots)

variable {D b l d : ℕ}

/-- Little-endian binary coordinates in the additive vector group. -/
def addressWord (D : ℕ) : Site D ≃ BitWord D := finFunctionFinEquiv.symm

theorem addressWord_bit (x : Site D) (i : Fin D) :
    finTwoEquiv (addressWord D x i) = x.val.testBit i.val := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change (finFunctionFinEquiv.symm x i == 1) = decide (x.val / 2 ^ i.val % 2 = 1)
  rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq, Fin.ext_iff,
    finFunctionFinEquiv_symm_apply_val]
  rfl

/-- The displacement of a stay or flip slot in binary address coordinates. -/
def stepShift (j : Fin D) (side : Bool) : BitWord D :=
  fun i ↦ if side = true ∧ j = i then 1 else 0

private theorem bit_add (a b : ZMod 2) :
    finTwoEquiv (a+b) = (finTwoEquiv a ^^ finTwoEquiv b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem addressWord_step (j : Fin D) (side : Bool) (x : Site D) :
    addressWord D (stepSite j side x) = addressWord D x + stepShift j side := by
  funext i
  apply finTwoEquiv.injective
  change finTwoEquiv (addressWord D (stepSite j side x) i) =
    finTwoEquiv (addressWord D x i + stepShift j side i)
  rw [bit_add, addressWord_bit, addressWord_bit]
  cases side with
  | false => simp [stepShift, finTwoEquiv]
  | true =>
    rw [stepSite_true_val, Nat.testBit_xor, Nat.testBit_two_pow]
    by_cases h : j = i
    · simp [h, stepShift, finTwoEquiv]
    · have hn : j.val ≠ i.val := fun e ↦ h (Fin.ext e)
      simp [h, hn, stepShift, finTwoEquiv]

/-- Reorder address coordinates into the chosen base and lane blocks. -/
def addressPartition (labels : Fin D ≃ Fin b ⊕ Fin l) : BitWord D ≃+ BitWord b × BitWord l where
  toEquiv := (labels.arrowCongr (Equiv.refl (ZMod 2))).trans (Equiv.sumArrowEquivProdArrow _ _ _)
  map_add' _ _ := rfl

/-- Change coordinates on positions, retaining the cursor in the base. -/
def lanePositions (labels : Fin D ≃ Fin b ⊕ Fin l) :
    (Fin D × Site D) ≃ (Fin D × BitWord b) × BitWord l :=
  ((Equiv.refl _).prodCongr ((addressWord D).trans (addressPartition labels).toEquiv)).trans
    (Equiv.prodAssoc _ _ _).symm

private def baseTarget (labels : Fin D ≃ Fin b ⊕ Fin l) (flip : Fin d → Bool) :
    Equiv.Perm ((Fin D × BitWord b) × Fin d) where
  toFun p := ((finRotate D p.1.1,
    p.1.2 + (addressPartition labels (stepShift p.1.1 (flip p.2))).1),p.2)
  invFun q :=
    let j := (finRotate D).symm q.1.1
    ((j, q.1.2 - (addressPartition labels (stepShift j (flip q.2))).1),q.2)
  left_inv _ := by simp only [Equiv.symm_apply_apply, add_sub_cancel_right]
  right_inv _ := by simp only [Equiv.apply_symm_apply, sub_add_cancel]

/-- A Section 7 lifted slot graph using any designated set of address bits as
lanes. Its arc displacements depend only on cursor and slot. -/
def laneGraph (labels : Fin D ≃ Fin b ⊕ Fin l) (flip : Fin d → Bool) (hD : 1 < D) :
    LiftedSlots (Fin D × BitWord b) d (BitWord l) where
  base.target := baseTarget labels flip
  base.ends_ne p he := by
    have : NeZero D := ⟨by omega⟩
    have hj : finRotate D p.1.1 = p.1.1 := congrArg Prod.fst he
    rw [finRotate_apply] at hj
    have hz : (1 : Fin D) = 0 := add_left_cancel (a := p.1.1) (by simpa using hj)
    have := congrArg Fin.val hz
    simp [Nat.mod_eq_of_lt hD] at this
  displacement p := (addressPartition labels (stepShift p.1.1 (flip p.2))).2

/-- The actual slot matching of the lifted network is the original cursor
advance and address step, transported by the position bijection. -/
theorem laneGraph_target (labels : Fin D ≃ Fin b ⊕ Fin l) (flip : Fin d → Bool) (hD : 1 < D)
    (j : Fin D) (x : Site D) (i : Fin d) :
    (laneGraph labels flip hD).actualGraph.target (lanePositions labels (j,x),i) =
      (lanePositions labels (finRotate D j, stepSite j (flip i) x),i) := by
  change (((finRotate D j, (addressPartition labels (addressWord D x)).1 +
      (addressPartition labels (stepShift j (flip i))).1),
      (addressPartition labels (addressWord D x)).2 +
        (addressPartition labels (stepShift j (flip i))).2),i) =
    (((finRotate D j, (addressPartition labels (addressWord D (stepSite j (flip i) x))).1),
      (addressPartition labels (addressWord D (stepSite j (flip i) x))).2),i)
  rw [addressWord_step, map_add]
  rfl

/-- The Section 7 matching is exactly the regularized cursor matching under
the position bijection, including all zero-width parallel slots. -/
theorem paddedLaneGraph_target {p : ℕ} (labels : Fin D ≃ Fin b ⊕ Fin l) (hD : 1 < D)
    (v : Position D) (i : Fin (2 + p)) :
    (laneGraph labels slotSide hD).actualGraph.target (lanePositions labels v, i) =
      ((lanePositions labels).prodCongr (Equiv.refl _)) ((paddedSlotGraph D p hD).target (v,i)) :=
  laneGraph_target labels slotSide hD v.1 v.2 i

/-- Each padded tensor-network edge is realized by the lifted slot matching
between its own two positions. -/
theorem paddedLaneGraph_edge {S : Type} [Fintype S] {p : ℕ} (labels : Fin D ≃ Fin b ⊕ Fin l)
    (hD : 1 < D) (bits : S → ℕ) (e : PaddedArc D p) :
    (laneGraph labels slotSide hD).actualGraph.target
        (lanePositions labels ((paddedNetwork D p bits).src e), (paddedEdgeEquiv D p e).2) =
      (lanePositions labels ((paddedNetwork D p bits).dst e), (paddedEdgeEquiv D p e).2) := by
  rw [paddedEdge_source, paddedLaneGraph_target]
  rw [show ((paddedEdgeEquiv D p e).1, (paddedEdgeEquiv D p e).2) = paddedEdgeEquiv D p e from rfl,
    paddedEdge_target hD bits]
  rfl

end CursorNetwork

end VPVNP
end Computability
end OAI
