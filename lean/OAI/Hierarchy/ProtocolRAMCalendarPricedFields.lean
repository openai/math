import OAI.Hierarchy.ProtocolRAMCalendarPricedBallot

namespace OAI
/-! # A priced histogram reads the same code, size and counters as the original admission pass -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage StockCommit PurchaseStage RepairHistogram
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {w q d : ℕ}

private theorem enough_yes (n : ℕ) (ask available : Fin n→Expr) (yes no : Expr) (cut : ℕ)
    (within : (ifEnough n ask available yes no).Fits w cut) : yes.Fits w cut := by
  induction n with
  | zero=>exact within
  | succ n ih=>exact ih _ _ within.2.2.2

private theorem enough_need (n : ℕ) (ask available : Fin n→Expr) (yes no : Expr) (cut : ℕ)
    (within : (ifEnough n ask available yes no).Fits w cut) (j : Fin n) : (ask j).Fits w cut := by
  induction n with
  | zero=>exact j.elim0
  | succ n ih=>exact Fin.cases within.2.1 (fun j=>ih _ _ within.2.2.2 j) j

private theorem admitted_inputs (b : Batch q d) (limit : ℕ)
    (valid : (invalidExpr b).Fits w limit) (positive : 0<q) :
    b.packet.Fits w limit ∧ (Expr.lookup b.termCount b.packet).Fits w limit ∧ ∀j,(b.field j).Fits w limit := by
  have good : (b.ifPacket (.lit 0) (.lit 1)).Fits w limit :=
    enough_yes d b.need b.stock _ _ limit valid.2.2.2.2.2.2
  have fallback : (ifHistogram q 0 b.field (.lit 0) (.lit 1)).Fits w limit:=valid.2.2.1
  refine ⟨valid.2.2.2.1,?_,fun j=>enough_need q b.field _ _ _ limit fallback j⟩
  cases q with
  | zero=>omega
  | succ q=>exact good.1.2.1

theorem priced_histogram_inputs (L : Dispatch) (B : Repair q d) (A : Area) (s : Sources) (g : LabelSource)
    (m : Memory w) (plan : AuditReady (audits L B) (postSnapshot L B m))
    (ordered : OrderedTallies (audits L B)) (endFlag : B.keys≤B.verdict) (stamp : B.keys≤g.out)
    (seed : g.out≤A.start) (positive : 0<q) (reg : Word w) :
    let b:=enabledBatch L B
    let before:=postSnapshot L B m
    let after:=stageInput A s g (postOutput L B m)
    b.packet.eval after reg=b.packet.eval before reg ∧
      b.termCount.read after (b.packet.eval after reg)=b.termCount.read before (b.packet.eval before reg) ∧
      ∀j,(b.field j).eval after reg=(b.field j).eval before reg := by
  intro b before after
  have inspection : (PurchaseStage.inspection L B).Fits w:=plan.1
  obtain ⟨valid,typed,_,_,_,_⟩:=inspection
  obtain ⟨packet,terms,fields⟩:=admitted_inputs b B.keys valid positive
  have low (u : Audit) (mem : u∈audits L B) : B.keys≤u.low := by
    change u∈Audit.check (PurchaseStage.inspection L B)::columns (writes L B) at mem
    rcases List.mem_cons.mp mem with rfl|rest
    · exact le_rfl
    · have later:=ordered.1 u rest
      change B.tally+1<u.low at later
      change B.keys+L.candidates≤B.tally at typed
      omega
  have kept (e : Expr) (fits : e.Fits w B.keys) : e.eval after reg=e.eval before reg :=
    (stage_input A s g _ e reg (ProtocolRAMGeneratedWrite.fits_mono _ stamp fits) seed).trans
      (post_input L B m e reg B.keys plan fits low endFlag)
  exact ⟨kept _ packet,kept _ terms,fun j=>kept _ (fields j)⟩

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
