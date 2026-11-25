import OAI.Hierarchy.TaggedWideDatedOperands
import OAI.Hierarchy.TaggedWireOriginalPublicRead

namespace OAI
/-! # A true two-sided RAM scan for each chronological half-edge family -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRows
open AdaptiveProbe ProtocolRAM RoleProgram WireTelescope
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing
variable {W n N : ℕ}

def visit (n : ℕ) (b : Bool) (i : Fin n) : Fin (n+n) :=
  if b then Fin.natAdd n i else Fin.castAdd n i

theorem visit_at (r : Fin (n+n)) : ∃b i,visit n b i=r := by
  refine Fin.addCases (fun i=>?_) (fun i=>?_) r
  · exact ⟨false,i,rfl⟩
  · exact ⟨true,i,rfl⟩

theorem each_read (left right : Expr) (m : Memory W) (fit : n+n≤2^W) (b : Bool) (i : Fin n) :
    (each n left right).eval m ((visit n b i).val:Word W)=(if b then right else left).eval m (i.val:Word W) := by
  have ni:=i.isLt
  have nFit : n<2^W := by omega
  have iFit := ni.trans nFit
  have hi : n+i.val<2^W := by omega
  cases b
  · simp [each,index,visit,Expr.eval,eval_atRow,Comparison.test,Fin.lt_def,Fin.val_cast_of_lt iFit,
      Fin.val_cast_of_lt nFit,ni]
  · have minus : ((n+i.val:ℕ):Word W)-(n:Word W)=(i.val:Word W) := by
      rw [Nat.cast_add]
      ring
    change (each n left right).eval m ((n + i.val : ℕ) : Word W) = right.eval m (i.val : Word W)
    have upper : ¬ (((n + i.val : ℕ) : Word W) < (n : Word W)) := by
      rw [Fin.lt_def, Fin.val_cast_of_lt hi, Fin.val_cast_of_lt nFit]
      exact Nat.not_lt_of_ge (Nat.le_add_right _ _)
    have test : Comparison.lt.test ((n + i.val : ℕ) : Word W) (n : Word W) = false :=
      decide_eq_false upper
    simp only [each, index, Expr.eval, eval_atRow, test, Bool.false_eq_true, ite_false,
      RowOp.opcode, BinaryOp.eval, minus]

theorem split_view (sock : Bool→Socket) (fit : n+n≤2^W) (m : Memory W) (i : Fin n) (b side : Bool) :
    (split n sock b).view m ((visit n side i).val:Word W)=
      (sock (if side then !b else b)).view m (i.val:Word W) := by
  cases side <;> simp [split,zipSocket,Socket.view,each_read _ _ m fit]

theorem split_resolved {S : PurchaseSampler} {h stage k attempts : ℕ} (chart : Chart) (sock : Bool→Socket)
    (fit : n+n≤2^W) (m : Memory W) (i : Fin n) (b side : Bool) (p : Public S h stage k attempts)
    (res : Resolved S chart (sock (if side then !b else b)) m (i.val:Word W) p) :
    Resolved S chart (split n sock b) m ((visit n side i).val:Word W) p :=
  resolved_congr S chart m _ _ _ _ _ (split_view sock fit m i b side) res

def stream (src : Fin n→Option (Fin N)) (sortSide : Fin N→Bool→Bool) : Fin (n+n) → Option (Fin N×Bool) :=
  Fin.addCases (fun i=>(src i).map (fun j=>(j,sortSide j false))) (fun i=>(src i).map (fun j=>(j,sortSide j true)))

theorem stream_at (src : Fin n→Option (Fin N)) (sortSide : Fin N→Bool→Bool) (b : Bool) (i : Fin n) :
    stream src sortSide (visit n b i)=(src i).map (fun j=>(j,sortSide j b)) := by
  cases b <;> simp only [visit, stream, Bool.false_eq_true, ite_false, ite_true, Fin.addCases_left, Fin.addCases_right]

theorem covers (src : Fin n→Option (Fin N)) (all : ∀j,∃i,src i=some j)
    (sortSide : Fin N→Bool→Bool) (onto : ∀j,Function.Surjective (sortSide j)) (i : Fin N) (side : Bool) :
    ∃r,stream src sortSide r=some (i,side) := by
  obtain ⟨q,hq⟩ := all i
  obtain ⟨b,hb⟩ := onto i side
  exact ⟨visit n b q,by simp [stream_at,hq,hb]⟩

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRows

end
end OAI
