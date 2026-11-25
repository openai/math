import OAI.Hierarchy.DescentRetainedRangeDigits
import OAI.Hierarchy.DescentBundleLanes
import OAI.Hierarchy.DescentLaneGates

namespace OAI
/-! # Range digits at each word of a two-lane equality gate -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentBundleHistory DescentKernelHistory DescentLaneGates DescentTerminalSliceRuns
noncomputable section
variable {A : Type} {width : A→ℕ} {Y p : ℕ}
variable (units : A→ℕ) (multiple : ∀a,width a=units a*p) (positive : 0<p)

def laneCode (l : Lane p width) : SliceCode:=⟨l.residue,l.stride,l.count units⟩

def operandCodes (o : Op Y p width) : List (List SliceCode) :=
  List.ofFn (fun j=>[laneCode units (o.arg j)])

theorem lane_codes (P : Program Y p width) (u : P.Node) :
    (ofProgram units multiple positive P).sliceFields u=operandCodes units (P.op u) :=by
  unfold Shape.sliceFields operandCodes
  apply congrArg List.ofFn
  funext j
  change (List.ofFn (fun _ : Fin 1=>laneCode units ((P.op u).arg j)))=_
  simp [List.ofFn_succ]

theorem equality_occurrences (P : Program Y p width) (u : P.Node) (l r : Lane p width)
    (eqOp : P.op u=equalOp (.wire l) (.wire r)) :
    occurrences (ofProgram units multiple positive P) u=
      List.replicate (l.count units) (laneCode units l)++List.replicate (r.count units) (laneCode units r) :=by
  have codes_eq := (lane_codes units multiple positive P u).trans (congrArg (operandCodes units) eqOp)
  calc
    _ = repeatFields ((ofProgram units multiple positive P).sliceFields u).flatten :=
      (layout (ofProgram units multiple positive P) u).symm
    _ = repeatFields (operandCodes units (equalOp (Y:=Y) (.wire l) (.wire r))).flatten :=
      congrArg (fun rows : List (List SliceCode) => repeatFields rows.flatten) codes_eq
    _ = _ := by simp [operandCodes,equalOp,List.ofFn_succ,repeatFields,laneCode]

/-- Padding after both real argument runs reads zero for all three words. -/
theorem equality_slot (P : Program Y p width) (u : P.Node) (l r : Lane p width)
    (eqOp : P.op u=equalOp (.wire l) (.wire r)) (slot : ℕ) (f : Fin 3) :
    atSlot (ofProgram units multiple positive P) u slot f=
      if slot<l.count units then value (laneCode units l) f
      else if slot-l.count units<r.count units then value (laneCode units r) f else 0 :=by
  unfold atSlot
  rw [equality_occurrences units multiple positive P u l r eqOp]
  by_cases left : slot<l.count units
  · rw [List.getElem?_append_left (by simpa using left)]
    simp [left]
  · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt left)]
    by_cases right : slot-l.count units<r.count units <;>
      simp [left,right]

end
end Hierarchy.DescentRetainedRangeDigits

end OAI
