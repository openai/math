import OAI.Hierarchy.TaggedWideDatedLayout
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # The two scaled original socket columns used once by all frozen formats -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM
open ProbeStage.CoreBoard.HistoryRoles RoleProgram
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Classical Fin.CommRing
variable {W T : ℕ} (p : Dated T) (work : ℕ) (side : Bool)
local notation "s" => p.slotPage work side
local notation "N" => p.rawEdges
local notation "B" => p.slotBase work side

/-- Two separate cleared n-word pages. Real normalized core or bought socket
identities are required only for represented rows; padding is still executed. -/
theorem slot_run (m : Memory W) (source : (p.orderedSlot side).Fits W B) (room : B+N+N+N<2^W) :
    ∃out,((s).code W).Exec m out (s).ticks ∧
      (∀i : Fin N,(p.slotBank work side).read out (i.val:Word W)=
        (p.lanes:Word W)*(p.orderedSlot side).eval m (i.val:Word W)) ∧
      ∀a,a<B-1 → out a=m a := by
  let result (i : Fin N) : Word W := (p.lanes:Word W)*(p.orderedSlot side).eval m (i.val:Word W)
  have valueFit : (s).value.Fits W B := by
    change (scale p.lanes (p.orderedSlot side)).Fits W B
    generalize p.lanes=n
    induction n with
    | zero=>trivial
    | succ n ih=>exact ⟨source,ih⟩
  have positive : 0<B := by simp [Dated.slotBase]
  have proof := ProtocolRAMTurnReplay.run (W:=W) B N (B+N) (B-1) (s).address (s).value m
    (fun i : Fin N=>B+i.val) result result (by trivial) valueFit le_rfl room (by omega)
    (by intro i;simp [Dated.slotPage,Expr.eval,RowOp.opcode,BinaryOp.eval,Nat.cast_add])
    (by intro i;exact eval_scale ..)
    (by intro i;right;have:=i.isLt;omega)
    (by intro i j h; exact congrArg result (Fin.ext (by omega)))
    (by intro j;right;exact ⟨j,rfl⟩)
  obtain ⟨out,ran,reads,keep⟩ := proof
  refine ⟨out,ran,?_,fun a ha=>keep a (Or.inl (by omega)) (Or.inl (by omega)) (by omega)⟩
  intro i
  have bound : N≤2^W := by omega
  have within : N≤(p.slotBank work side).size := (ProtocolRAMPurchaseSampler.lt_span N).le
  change out (B+(i.val:Word W).val%(p.slotBank work side).size)=_
  rw [Fin.val_cast_of_lt (i.isLt.trans_le bound),Nat.mod_eq_of_lt (i.isLt.trans_le within)]
  exact reads i

/-- Both oriented socket banks from the same event history survive the second
native scatter. Both source expressions read the same pre-scatter configuration. -/
theorem slot_pair_run (m : Memory W)
    (fits : ∀b,(p.orderedSlot b).Fits W (p.slotStart work)) (room : p.workEnd work<2^W) :
    ∃out,(((p.slotPage work false).code W).seq ((p.slotPage work true).code W)).Exec m out
      ((p.slotPage work false).ticks+(p.slotPage work true).ticks) ∧
      (∀b (i : Fin N),(p.slotBank work b).read out (i.val:Word W)=
        (p.lanes:Word W)*(p.orderedSlot b).eval m (i.val:Word W)) ∧
      ∀a,a<p.slotStart work → out a=m a := by
  have lo : p.slotBase work false=p.slotStart work+1 := by simp [Dated.slotBase]
  have hi : p.slotBase work true=p.slotStart work+1+3*N+1 := by simp [Dated.slotBase]; omega
  have last : p.workEnd work=p.slotStart work+2*(1+3*N) := rfl
  obtain ⟨mid,left,readL,keepL⟩ := slot_run p work false m
    (ProtocolRAMGeneratedWrite.fits_mono _ (by omega) (fits false)) (by omega)
  obtain ⟨out,right,readR,keepR⟩ := slot_run p work true mid
    (ProtocolRAMGeneratedWrite.fits_mono _ (by omega) (fits true)) (by omega)
  refine ⟨out,left.then right,?_,fun a ha=>(keepR a (by omega)).trans (keepL a (by omega))⟩
  intro b j
  cases b with
  | false =>
    rw [←readL j]
    change out (p.slotBase work false+(j.val:Word W).val%(p.slotBank work false).size) =
      mid (p.slotBase work false+(j.val:Word W).val%(p.slotBank work false).size)
    have h := j.isLt
    have span : N≤(p.slotBank work false).size := (ProtocolRAMPurchaseSampler.lt_span _).le
    rw [Fin.val_cast_of_lt (show j.val<2^W by omega),Nat.mod_eq_of_lt (h.trans_le span)]
    exact keepR _ (by omega)
  | true =>
    rw [readR]
    exact congrArg _ (eval_below (p.orderedSlot true) _ m mid (fits true) (fun a h=>keepL a (by omega)))


end Hierarchy.ProtocolRAM.Calendar.WideCPU

end
end OAI
