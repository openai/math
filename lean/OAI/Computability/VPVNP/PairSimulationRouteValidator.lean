import OAI.Computability.VPVNP.PairSimulationRouteSuccessors
import OAI.Computability.VPVNP.PairSimulationRoutePhases
import OAI.Computability.VPVNP.PairSimulationRouteTiming
import OAI.Computability.VPVNP.PairSimulationMapLookup

/-!
# Executing the native routing checker on a cursor vertex

The scheduler starts by clearing the mask and offset. After the successor
fields it switches to the sorting-block width. The final jump tests the mask
accumulated over both passes. All inputs, including inconsistent four-port
buffers, reach their continuation within the same clock bound.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RouteSchedule

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord CursorRouting CursorNetwork RAMLayout
open scoped Fin.CommRing

variable {D H w W p r k : ℕ}

variable [NeZero D] {P : Program p r} {M : Machine W p r k}

/-- Run the linked scheduler on the resident buffers. It consumes only local ticks,
preserves both memories, and jumps according to the exact routing predicate. -/
theorem native_exact (hl : P.Linked M) (v : Position D) (buf : Buffers D H w)
    (base : LocalPort → Word W) (c : Config W p r) (hc : c.pc = P.pc 0)
    (inp : Inputs P.reg v buf base c) (hwidth : c.reg (P.reg 21) = ((8 * w : ℕ) : Word W))
    (hw : D < W) (hsucc : 8 * w < 2 ^ W) (hsort : blockBits H w < 2 ^ W) :
    ∃ d, Prefix M c (List.replicate (routeTicks W v H w) .tick) d ∧
      d.pc = (if routeAccept H w v (readBuffer buf) then P.yes else P.no) ∧
      RouteRange.Frame (Keep P.reg) c d := by
  have control (i : Fin 7) (q : Config W p r) (hp : q.pc = P.pc i) :
      M.program.step q = (P.instruction i).run M.publicData q := by
    change (M.code q.pc).run M.publicData q = _
    rw [hp, hl.control i]
  let clear := c.put (P.pc 1) (P.reg 22) 0
  let start := clear.put (P.succ 0) (P.reg 16) 0
  have pre : Prefix M c (List.replicate 2 .tick) start :=
    .tick (control 0 c hc) (.tick (control 1 clear rfl) (.nil _))
  have f₀ : RouteRange.Frame (Keep P.reg) c start :=
    ((RouteRange.Frame.refl c).put (P.pc 1) (P.reg 22) 0
      (fun _ h ↦ h.1.1.1 22 (by decide))).put (P.succ 0) (P.reg 16) 0
        (fun _ h ↦ h.1.1.2.2)
  have width : start.reg (P.reg 21) = ((8*w : ℕ) : Word W) := by
    simp [start, clear, Config.put, hwidth]
  have off : start.reg (P.reg 16) = 0 := by simp [start]
  have mask : start.reg (P.reg 22) = 0 := by simp [start, clear, Config.put]
  obtain ⟨s, succRun, sPC, _, sState⟩ :=
    successors_exact hl v buf base start rfl (inp.transfer f₀) width off hw hsucc
  have fs := f₀.trans (narrowFrame sState.toFrame (fun _ h ↦ keep_successor P h))
  let switch := s.put (P.phase 0) (P.reg 21) (s.reg (P.reg 29))
  have changeWidth : Prefix M s (List.replicate 1 .tick) switch :=
    .tick (control 3 s sPC) (.nil _)
  have switched := fs.put (P.phase 0) (P.reg 21) (s.reg (P.reg 29)) (fun _ h ↦ h.2)
  have swidth : switch.reg (P.reg 21) = (blockBits H w : Word W) := by
    simpa [switch] using (inp.transfer fs).sortWidth
  have soff : switch.reg (P.reg 16) = ((D*(8*w) : ℕ) : Word W) := by
    simpa [switch, Config.put, off] using sState.offset
  have smask : switch.reg (P.reg 22) = 0 ↔ ∀ j : Fin D, RouteCall.Good v buf (.inl j) := by
    change Function.update s.reg (P.reg 21) _ (P.reg 22) = 0 ↔ _
    rw [Function.update_of_ne (P.reg.injective.ne (by decide)), sState.maskEq, mask]
    exact ⟨fun h j ↦ h.2 j j.isLt, fun h ↦ ⟨rfl, fun j _ ↦ h j⟩⟩
  obtain ⟨l, layerRun, lPC, _, lState⟩ :=
    phases_exact hl v buf base switch rfl (inp.transfer switched) swidth soff hw hsort
  have fl := switched.trans (narrowFrame lState.toFrame (fun _ h ↦ h.1))
  have ok : l.reg (P.reg 22) = 0 ↔ routeAccept H w v (readBuffer buf) = true := by
    rw [lState.maskEq, smask, RouteCall.routeAccept_iff_good]
    constructor
    · rintro ⟨h₁,h₂⟩ (j | a)
      · exact h₁ j
      · exact h₂ a a.phase_lt
    · exact fun h ↦ ⟨fun j ↦ h (.inl j), fun a _ ↦ h (.inr a)⟩
  let final := {l with pc := if routeAccept H w v (readBuffer buf) then P.yes else P.no}
  have dispatch : Prefix M l (List.replicate 1 .tick) final := by
    apply Prefix.tick _ (.nil _)
    rw [control 6 l lPC]
    change CallAction.localStep {l with pc := if l.reg (P.reg 22) = l.reg (P.reg 17)
      then P.yes else P.no} = _
    simp only [(inp.transfer fl).zero, ok, final]
  refine ⟨final, ?_, rfl, ⟨fl.regs, fl.memory, fl.persistent⟩⟩
  unfold routeTicks
  repeat rw [List.replicate_add]
  exact (((pre.append succRun).append changeWidth).append layerRun).append dispatch

/-- Every resident input reaches its routing continuation within the scheduler clock. -/
theorem native (hl : P.Linked M) (v : Position D) (buf : Buffers D H w)
    (base : LocalPort → Word W) (c : Config W p r) (hc : c.pc = P.pc 0)
    (inp : Inputs P.reg v buf base c) (hwidth : c.reg (P.reg 21) = ((8 * w : ℕ) : Word W))
    (hw : D < W) (hsucc : 8 * w < 2 ^ W) (hsort : blockBits H w < 2 ^ W) :
    ∃ t d, t ≤ clock D H w ∧ Prefix M c (List.replicate t .tick) d ∧
      d.pc = (if routeAccept H w v (readBuffer buf) then P.yes else P.no) ∧
      RouteRange.Frame (Keep P.reg) c d := by
  obtain ⟨d, pre, hp, frame⟩ := native_exact hl v buf base c hc inp hwidth hw hsucc hsort
  exact ⟨_, d, routeTicks_le W v H w, pre, hp, frame⟩

/-- With a rejecting instruction at the failed exit, every failed route rejects
on every branch tape and external memory, including at budgets shorter than its scan. -/
theorem native_reject (hl : P.Linked M) (v : Position D) (buf : Buffers D H w)
    (base : LocalPort → Word W) (c : Config W p r) (hc : c.pc = P.pc 0)
    (inp : Inputs P.reg v buf base c) (hwidth : c.reg (P.reg 21) = ((8 * w : ℕ) : Word W))
    (hw : D < W) (hsucc : 8 * w < 2 ^ W) (hsort : blockBits H w < 2 ^ W)
    (failed : routeAccept H w v (readBuffer buf) = false) (hbad : M.code P.no = .reject)
    (fuel : ℕ) (mem : Memory W) (bits : List Bool) : execute M.program fuel c mem bits = none := by
  obtain ⟨_, d, _, pre, hp, _⟩ := native hl v buf base c hc inp hwidth hw hsucc hsort
  have bad : d.pc = P.no := by simpa [failed] using hp
  exact MapLookup.reject_after_ticks pre (fun _ h ↦ List.eq_of_mem_replicate h)
    (bad ▸ hbad) fuel mem bits

end PairSimulation.RouteSchedule

end VPVNP
end Computability
end OAI
