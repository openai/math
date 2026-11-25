import OAI.Hierarchy.GridOrderedSources
import OAI.Hierarchy.GridDescription
import OAI.Hierarchy.GridNativeEvaluator
import OAI.Hierarchy.GridApproximationAdvice

namespace OAI
/-! # The grid emitter and its selector-independent cost -/

noncomputable section
namespace Hierarchy.GridCompilerAdmission
open ThreeFlat Diagonal RAM ContinuationLink PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM UniversalGrid GridThrough
open scoped Fin.CommRing

variable {F : Type} [Field F] [Fintype F] {w k n p e ell : ℕ}
variable (X : Catalyst.Approximation F k p)

def arena (w : ℕ) : GridOrderedSources.Arena := ⟨GridDescription.sector w⟩

def emit (dispatch : Procedure (64*w)) (wB : ℕ) (n k p e limit : ℕ) (size : ℕ)
    (zero one : Word (64*w)) : Procedure (64*w) :=
  ((GridApproximationAdvice.loader w wB (e*2+w^2) (2*GridDescription.sector w)).seq dispatch).seq
    (GridOrderedSources.writing (arena w) k n p e wB limit size zero one)

def clock (w k n e B limit nav : ℕ) :=
  4000*(w*B)+nav+GridOrderedSources.clock k n e B limit

/-- All size dependence outside the native dispatcher is in words and loop
trips. This is the cutoff used when choosing the evaluator's architecture. -/
theorem hardware (nav : Procedure (64*w)) (B n k p e limit size : ℕ) (zero one : Word (64*w)) :
    let P := emit nav B n k p e limit size zero one
    P.labels+P.registers+P.slots ≤ nav.labels+nav.registers+nav.slots+100027 := by
  let b := GridOrderedSources.writing (arena w) k n p e B limit size zero one
  have sizeB : b.labels+b.registers+b.slots≤100000 :=
    GridOrderedSources.hardware (arena w) k n p e B limit size zero one
  change (15+nav.labels+b.labels)+(8+nav.registers+b.registers)+(4+nav.slots+b.slots)≤_
  omega

omit [Field F] in
/-- Total charged time on the real evaluator after a selector branch, with
the sender scans, ordered writer and final weighted contraction included.
The only branch-dependent cost is the measured navigation time. -/
theorem charged_path {B : ℕ} (nav : ℕ) (positive : 0<B) (size : X.size≤B)
    (rails : e*(n+1)≤2*k*((n+1)^k*B)) (selector : ell≤(n+1)^k*B) :
    let L := (n+1)^k*B
    let cutoff := GridPaddedCellImage.limit e ((n+1)^k) B (Ordered.hiddenCount e n)
      (Ordered.edgeCount e n) (Fintype.card F)
    (GridNativeEvaluator.tailTime (n:=n) (e:=e) X + clock w k n e B cutoff nav)+4+5*ell ≤
      nav+(12000000*(k+1)+4000*w)*L+45000*((Fintype.card F)^2+11) := by
  intro L cutoff
  have limit := GridPaddedCellImage.linear_limit (F:=F) rails
  have tail := GridNativeEvaluator.path_bound (e:=e) (n:=n) X size rails
  have t : GridNativeEvaluator.tailTime (n:=n) (e:=e) X ≤
      (400*k+40)*L+(Fintype.card F)^2+11 :=
    (Nat.le_add_right _ _).trans tail
  have ea : e≤e*(n+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have bl : B≤L := Nat.le_mul_of_pos_left _ (Nat.pow_pos (Nat.succ_pos _))
  have kl : (n+1)^k*k≤k*L := by
    rw [Nat.mul_comm _ k]
    exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ positive)
  have positiveL : 1≤L := positive.trans_le bl
  have costRows : GridOrderedEdgeRAM.totalWords e n≤12*(e*(n+1)) := by
    unfold GridOrderedEdgeRAM.totalWords Ordered.edgeCount
    nlinarith only [ea]
  change cutoff≤(250*k+40)*L+(Fintype.card F)^2+11 at limit
  change e*(n+1)≤2*k*L at rails
  have cp : (n+1)^k*k*B=k*L := by dsimp only [L]; ring
  unfold clock GridOrderedSources.clock
  rw [cp]
  have cells : (n+1)^k*B=L := rfl
  change ell≤L at selector
  nlinarith only [cells,t,limit,Nat.mul_le_mul_left (4000*w) bl,ea,kl,positiveL,rails,selector,costRows,
    Nat.zero_le (k*L),Nat.zero_le ((Fintype.card F)^2)]

end Hierarchy.GridCompilerAdmission
end

end OAI
