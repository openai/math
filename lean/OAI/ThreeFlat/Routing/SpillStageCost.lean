import OAI.ThreeFlat.Routing.SpillTwoPass
import OAI.ThreeFlat.Routing.SpillControlCost

namespace OAI
/-! # Size of a complete sparse two-pass compaction stage -/

noncomputable section
open scoped BigOperators Classical
namespace ThreeFlat.Routing.Spill
open Concentrator

def bankCharge (D : ℕ) := controlCharge D + 48*D + 2^(2*D+1)*(2*D+3)

theorem twoPassStage_cells {C q D R : ℕ} (B : TwoPassBank C q D R) {F : Type*}
    [CommSemiring F] (w : ℕ) :
    (twoPassStage (F := F) B w).network.cells ≤
      (C+1)*R*(Nat.log 2 (C*R)+w+3)*bankCharge D := by
  let m := (C+1)*R*(Nat.log 2 (C*R)+w+3)
  let K := controlCharge D
  let L := 2^(2*D+1)*(2*D+3)
  have larger : C*R ≤ (C+1)*R := Nat.mul_le_mul_right R (Nat.le_succ C)
  have hr : R ≤ (C+1)*R := Nat.le_mul_of_pos_left _ (by omega)
  have m0 : C*R*(Nat.log 2 (C*R)+2) ≤ m :=
    Nat.mul_le_mul larger (by omega)
  have m1 : C*R ≤ m := larger.trans (Nat.le_mul_of_pos_right _ (by omega))
  have m2 : R*(w+1) ≤ m := Nat.mul_le_mul hr (by omega)
  have c0 := (twoPassBank_control_cells (F := F) B).trans (Nat.mul_le_mul_right _ m0)
  have count : Fintype.card (Candidate (fullBoard B)) ≤ C*R*(3*D) := by
    calc
      _ = ∑ e : Fin (C*R), (fullBoard B e).card := by simp [Candidate,Fintype.card_sigma]
      _ ≤ ∑ _ : Fin (C*R), 3*D := Finset.sum_le_sum (fun e _ => fullBoard_left B e)
      _ = _ := by simp
  have c1 : Fintype.card (Candidate (fullBoard B))*16 ≤ m*(48*D) := by
    calc
      _ ≤ m*(3*D)*16 := Nat.mul_le_mul_right _ (count.trans (Nat.mul_le_mul_right _ m1))
      _ = _ := by ring
  have c2 : (linkNetwork (F := F) (fullBoard B) w).cells ≤ m*L :=
    (by simpa only [Fintype.card_fin] using
      linkNetwork_cells (F := F) (fullBoard B) w D (fullBoard_right B) :
      (linkNetwork (F := F) (fullBoard B) w).cells ≤ R*(w+1)*L).trans (Nat.mul_le_mul_right _ m2)
  unfold twoPassStage
  rw [packingStage_cells,boardCheck_cells]
  exact (Nat.add_le_add (Nat.add_le_add c0 c1) c2).trans_eq (by
    change m*K + m*(48*D) + m*L = m*(K + 48*D + L)
    ring)

end ThreeFlat.Routing.Spill

end
end OAI
