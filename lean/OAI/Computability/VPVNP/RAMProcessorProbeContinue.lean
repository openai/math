import OAI.Computability.VPVNP.RAMProcessorProbeStep
import OAI.Computability.VPVNP.RAMProcessorProbeFailure

/-!
# Resuming the physical call after an admitted probe

The native read continuation sees the exact guessed value. The write
continuation sees its original register bank. Both consume precisely the
probe just staged and recorded by the graph.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor.ProbeStep

open BurstRAM PrivateRAM RAMSerialization

variable {w p r k H F : ℕ} {hw : 2 ≤ w}

/-- Native read or write event corresponding to the staged probe. Its address comes from the
original register bank even if a read overwrites the address register. -/
def event (a : ProbeStep w p r) (s : Snapshot w p r k) : Event w :=
  match a with
  | .read _ i _ v _ => .read (s.cfg.reg i) v
  | .write i j _ => .write (s.cfg.reg i) (s.cfg.reg j)

theorem link (a : ProbeStep w p r) (s : Snapshot w p r k) (start ord : Word w) (hc ho) :
    ProbeLink s (a.finish s hw start ord hc ho) (a.record s start ord) (a.event s) start ord ⟨ord.val+1,ho⟩ := by
  cases a <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,fun _ => rfl,fun _ => rfl⟩

theorem finish_fuel (a : ProbeStep w p r) (s : Snapshot w p r k) (start ord : Word w) (hc ho) :
    (a.finish s hw start ord hc ho).fuel = s.fuel := by cases a <;> rfl

theorem finish_pc (a : ProbeStep w p r) (s : Snapshot w p r k) (start ord : Word w) (hc ho) :
    (a.finish s hw start ord hc ho).cfg.pc = a.next := by cases a <;> rfl

theorem pending_eq (a : ProbeStep w p r) (T : Template p r k) (s : Snapshot w p r k)
    (start ord : Word w) (hc ho) (hp : 0 < allowance s) (hb : a.accepts s) :
    let u := a.finish s hw start ord hc ho
    pending T s a.callback = LocalProcessor.addEvent (a.event s)
      (runLocalCall (T.instantiate w u.pub).logProgram u.fuel u.cfg (allowance u) u.choices).output := by
  dsimp only
  rw [a.finish_allowance s hw start ord hc ho hp]
  have he : allowance s = (allowance s-1)+1 := by omega
  cases a with
  | read dst addr pc v tail =>
    have hg := (takeWord_eq_some_iff s.choices v tail).mpr hb
    unfold pending LocalProcessor.resume
    conv_lhs => rw [he]
    simp only [callback, ISA.Callback.action, hg, Option.bind_some]
    rfl
  | write addr src pc =>
    unfold pending LocalProcessor.resume
    conv_lhs => rw [he]
    rfl

/-- Inductively transfer the entire successful or failed continuation. -/
theorem continue_run (a : ProbeStep w p r) (T : Template p r k) {s : Snapshot w p r k} {ys start ord}
    (hin : InCall hw H F s ys start ord) (hp : 0 < allowance s) (hb : a.accepts s)
    (ih : let u := a.finish s hw start ord (hin.costRoom hp) hin.ordRoom
      InCall hw H F u (ys++[a.record s start ord]) start ⟨ord.val+1,hin.ordRoom⟩ →
        ∃ n ≤ (u.fuel+1)*segmentWork w F, SegmentRun T hw H F u (ys++[a.record s start ord])
          start ⟨ord.val+1,hin.ordRoom⟩ n) :
    ∃ d ≤ 200*(w+1) + (s.fuel+1)*segmentWork w F,
      Meets T hw H F s ys start ord (.callback a.callback) (pending T s a.callback) d := by
  let u := a.finish s hw start ord (hin.costRoom hp) hin.ordRoom
  obtain ⟨d, hd, hrun, hnext⟩ := a.run T hin hp hb
  obtain ⟨t, ht, tail⟩ := ih hnext
  rw [a.finish_fuel] at ht
  rw [← a.finish_pc s start ord (hin.costRoom hp) hin.ordRoom (hw := hw)] at hrun
  exact ⟨d+t, Nat.add_le_add hd ht, probe_then_segment T hrun (a.link ..)
    (a.pending_eq T s start ord (hin.costRoom hp) hin.ordRoom hp hb) tail⟩

end RAMTape.SiteProcessor.ProbeStep

end VPVNP
end Computability
end OAI
