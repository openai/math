import OAI.Computability.VPVNP.RAMProcessorReportPrefix
import OAI.Computability.VPVNP.RAMProcessorGraphProbe

/-!
# External callbacks after a bounded private segment

The pending result uses the unspent fuel and the three probe allowances in
the physical bank. Connecting it to the internal scan preserves the full
report, including private choices that did not create memory records.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor

open BurstRAM PrivateRAM RAMSerialization

variable {w p r k H F : ℕ} {hw : 2 ≤ w}

/-- Resume the native log program at a physical callback using the snapshot's remaining
instruction fuel, probe allowance and private choice stream. -/
def pending (T : Template p r k) (s : Snapshot w p r k) (cb : ISA.Callback p r) :=
  LocalProcessor.resume (T.instantiate w s.pub).logProgram (allowance s)
    ⟨cb, s.cfg, s.fuel, s.choices, []⟩

/-- Specification of a physical run from a given label for a pending native result. Failure
reaches a rejecting row. Success reaches the iteration label with the matching report,
record buffer and unused choice suffix. -/
def Meets (T : Template p r k) (hw : 2 ≤ w) (H F : ℕ) (s : Snapshot w p r k)
    (ys : List (WordRecord w)) (start ord : Word w) (l : Label p r) (out : LocalProcessor.Output w) (t : ℕ) : Prop :=
  match out with
  | none => RejectRun (table T) t (atLabel T l) s.bank
  | some (rep, tail) => ∃ u new, CallReady hw H F false u new ∧ CallReturn s u ys new start ord rep tail ∧
      StackRuns (table T) t (atLabel T l) s.bank (atLabel T .iteration) u.bank

theorem scan_then_pending (T : Template p r k) (s : Snapshot w p r k) {ys start ord t d}
    (run : let y := LocalProcessor.scan T s.pub s.fuel s.cfg s.choices
      StackRuns (table T) t (atLabel T (.segment s.cfg.pc)) s.bank (atLabel T (.callback y.exit))
        (s.afterLocal y).bank)
    (hr : let y := LocalProcessor.scan T s.pub s.fuel s.cfg s.choices
      Meets T hw H F (s.afterLocal y) ys start ord (.callback y.exit) (pending T (s.afterLocal y) y.exit) d) :
    SegmentRun T hw H F s ys start ord (t+d) := by
  let y := LocalProcessor.scan T s.pub s.fuel s.cfg s.choices
  let out := pending T (s.afterLocal y) y.exit
  have eqout : (runLocalCall (T.instantiate w s.pub).logProgram s.fuel s.cfg (allowance s) s.choices).output =
      out.map (fun z => (z.1.withEvents y.prefixEvents, z.2)) := by
    rw [← LocalProcessor.scan_result, LocalProcessor.result, LocalProcessor.addEvents_eq]
    rfl
  change Meets T hw H F (s.afterLocal y) ys start ord (.callback y.exit) out d at hr
  unfold SegmentRun
  unfold allowance at eqout
  rw [eqout]
  cases ho : out with
  | none =>
    change RejectRun (table T) (t+d) (atLabel T (.segment s.cfg.pc)) s.bank
    rw [ho] at hr
    exact run.thenReject hr
  | some z =>
    obtain ⟨rep,tail⟩ := z
    rw [ho] at hr
    obtain ⟨u, zs, ready, ret, finish⟩ := hr
    exact ⟨u,zs,ready,ret.privatePrefix T,run.trans finish⟩

private theorem callReady_return {s : Snapshot w p r k} {ys start ord} (hin : InCall hw H F s ys start ord)
    (src : Fin r) : CallReady hw H F false (s.afterReturn src) ys := by
  exact {hin.toCallReady with buffer := {
    fit := hin.buffer.fit, scratch := rfl, zeros := rfl, remaining := hin.buffer.remaining,
    buffer := hin.buffer.buffer, output := hin.buffer.output }}

private theorem callReady_accept {s : Snapshot w p r k} {ys start ord} (hin : InCall hw H F s ys start ord) :
    CallReady hw H F false s.afterAccept ys := by
  exact {hin.toCallReady with buffer := {
    fit := hin.buffer.fit, scratch := rfl, zeros := rfl, remaining := hin.buffer.remaining,
    buffer := hin.buffer.buffer, output := hin.buffer.output }}

theorem pending_return (T : Template p r k) {s : Snapshot w p r k} {ys start ord}
    (hin : InCall hw H F s ys start ord) (src : Fin r) :
    Meets T hw H F s ys start ord (.callback (.returnState src)) (pending T s (.returnState src)) (8*w+6) := by
  refine ⟨s.afterReturn src, ys, callReady_return hin src, ?_, returnState_run T s src⟩
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,by simp [Report.probes,countProbes]; rfl,rfl,
    by simp [Report.probes,countProbes]; rfl,rfl,by simp [eventRecords]⟩

theorem pending_accept (T : Template p r k) {s : Snapshot w p r k} {ys start ord}
    (hin : InCall hw H F s ys start ord) :
    Meets T hw H F s ys start ord (.callback .accept) (pending T s .accept) 3 := by
  refine ⟨s.afterAccept, ys, callReady_accept hin, ?_, accept_run T s⟩
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,by simp [Report.probes,countProbes]; rfl,rfl,
    by simp [Report.probes,countProbes]; rfl,rfl,by simp [eventRecords]⟩

theorem pending_reject (T : Template p r k) (s : Snapshot w p r k) (ys : List (WordRecord w)) (start ord : Word w) :
    Meets T hw H F s ys start ord (.callback .reject) (pending T s .reject) 1 := by
  exact ⟨atLabel T .reject, s.bank, .cons (.goto rfl) (.nil ..), rfl⟩

end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
