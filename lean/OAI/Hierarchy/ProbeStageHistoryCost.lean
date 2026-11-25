import OAI.Hierarchy.ProbeStageHistory
import OAI.Hierarchy.ProbeSaturationCost

namespace OAI
/-! # Actual candidate probes and saturated lists along the retained history -/

namespace Hierarchy.ProbeStage
open Finset
open scoped BigOperators
noncomputable section

def expectedScans (h d : ℕ) (π : Equiv.Perm (Fin (2^h))) (j : ℕ) (r : Fin (2^h)) : ℕ := by
  classical
  exact if r∈(formatAdvice h d).fallbacks (radix_pos h d) (history h d π j).tiles then radix h d else 0

def expectedClears (h d : ℕ) (π : Equiv.Perm (Fin (2^h))) (j : ℕ) (r : Fin (2^h)) :=
  let str := (formatAdvice h d).row
  let a := allocateMasked (history h d π j).tiles (radix_pos h d) str
  saturationWrites str (a.color r) (a.enterRank r)+saturationWrites str (a.color r) (a.exitRank r)

private theorem walk_inspections {B ℓ n : ℕ} (A : MaskAdvice B ℓ) (pos : 0<B)
    (q : ℕ) (p : Matching n) : A.inspections pos q p.tiles =
    ∑ j∈range q,B*(A.fallbacks pos (Matching.walk pos A.row p j).tiles).card := by
  induction q generalizing p with
  | zero => simp [MaskAdvice.inspections]
  | succ q ih =>
    rw [Finset.sum_range_succ']
    change B*(A.fallbacks pos p.tiles).card+A.inspections pos q (Matching.descend pos A.row p).tiles=_
    rw [ih]
    rw [Nat.add_comm (B*(A.fallbacks pos p.tiles).card) _]
    apply congrArg (· + B*(A.fallbacks pos p.tiles).card)
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg (fun x : Matching n => B*(A.fallbacks pos x.tiles).card)
      (Matching.walk_succ pos A.row p k).symm

theorem scans_history (h d : ℕ) (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) :
    ∑ j∈range (rounds d),∑ r,expectedScans h d π j r ≤ rounds d*(2*4^rounds d*2^h) := by
  have per (j : ℕ) : ∑ r,expectedScans h d π j r =
      radix h d*((formatAdvice h d).fallbacks (radix_pos h d) (history h d π j).tiles).card := by
    classical
    simp [expectedScans,Nat.mul_comm]
  simp_rw [per]
  have cost := permutation_inspections_linear h d hd π
  have counts := walk_inspections (formatAdvice h d) (radix_pos h d) (rounds d) (Matching.root π)
  exact counts.symm.le.trans cost

theorem clears_history (h d : ℕ) (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) :
    ∑ j∈range (rounds d),∑ r,expectedClears h d π j r ≤ rounds d*(2*(288*d+17)*4^rounds d*2^h) := by
  let B := radix h d
  let str := (formatAdvice h d).row
  have per (j : ℕ) (hj : j<rounds d) : ∑ r,expectedClears h d π j r ≤ 2*(288*d+17)*4^rounds d*2^h := by
    let p := (history h d π j).tiles
    have clear := saturation_both_sides p (radix_pos h d) (allocateMasked p (radix_pos h d) str) str
    have dims := history_sizes hd π (Nat.le_of_lt hj)
    let k := B^j*blocks (2^widthLog h d j) B
    let t := B^4*(8*(4*h+2))
    have cap := occurrences_at_depth (h:=h) hd (Nat.le_of_lt hj)
    change k*(t+B)≤_ at cap
    have limit : 2*(Fintype.card (history h d π j).shape.Group*blocks (history h d π j).shape.span B)*t =
        2*k*t := by rw [history_card π j,dims.1,dims.2]
    have writes : ∑ r,expectedClears h d π j r≤2*k*t := clear.trans_eq limit
    have probe : 2*k*t≤2*(k*(t+B)) := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left k (Nat.le_add_right _ _))
    have power := Nat.pow_le_pow_right (by decide : 0<4) hj.le
    calc
      _ ≤ 2*(k*(t+B)) := writes.trans probe
      _ ≤ 2*((288*d+17)*4^j*2^h) := Nat.mul_le_mul_left _ cap
      _ = 2*(288*d+17)*4^j*2^h := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ power)
  exact (Finset.sum_le_sum (s:=range (rounds d)) (fun j hj => per j (mem_range.mp hj))).trans_eq (by simp)

end
end Hierarchy.ProbeStage

end OAI
