import OAI.Computability.VPVNP.PairSimulationRouteTiming

/-!
# Checking the successor fields in cursor-bit order

The counted range starts at offset zero. For each cursor bit it calls the
native routing checker on the corresponding successor field and then advances
the common offset by eight guest words. Its mismatch mask records exactly
the failed successor checks on the four resident half-wire buffers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RouteSchedule

open BurstRAM PrivateRAM PrimedCounter.GuessWord CursorRouting CursorNetwork
open scoped Fin.CommRing

variable {D H w W p r k : ℕ} [NeZero D]

theorem successors_exact {P : Program p r} {M : Machine W p r k} (hl : P.Linked M)
    (v : Position D) (buf : Buffers D H w) (base : LocalPort → Word W) (c : Config W p r)
    (hc : c.pc = P.succ 0) (inp : Inputs P.reg v buf base c)
    (hwidth : c.reg (P.reg 21) = ((8 * w : ℕ) : Word W))
    (hoff : c.reg (P.reg 16) = 0) (hW : D < W) (hfit : 8 * w < 2 ^ W) :
    ∃ d, Prefix M c (List.replicate (succTicks W v H w) .tick) d ∧
      d.pc = P.pc 3 ∧ d.reg (P.reg 3) = (D : Word W) ∧
      RouteRange.Partial (RangeKeep P.reg 3) (P.reg 16) (P.reg 22) (8 * w) D
        (fun i : Fin D ↦ RouteCall.Good v buf (.inl i)) c d := by
  have widthKeep := rangeKeep_reg P.reg 3 21 (by decide) (by decide) (by decide)
  apply RouteRange.run_exact hl.successors (hl.control 2) D (8 * w)
    (fun i ↦ RouteCall.ticks W v (.inl i) (8 * w))
    (hW.trans Nat.lt_two_pow_self) (fun i ↦ RouteCall.Good v buf (.inl i)) (RangeKeep P.reg 3)
    (rangeKeep_reg P.reg 3 2 (by decide) (by decide) (by decide))
    (rangeKeep_reg P.reg 3 23 (by decide) (by decide) (by decide))
    widthKeep (fun _ h ↦ h.2) (P.reg.injective.ne (by decide)) (P.reg.injective.ne (by decide))
    (P.reg.injective.ne (by decide)) c hc inp.dimension inp.one hwidth
  intro i q body index partialRun
  have ready := inp.transfer (narrowFrame partialRun.toFrame (fun _ h ↦ keep_successor P h))
  have callReady : RouteCall.Ready (H := H) (w := w) P.reg v (.inl i) base q := by
    refine ⟨⟨ready.cursor, ready.site, ready.dimension, index, fun _ he ↦ nomatch he⟩,
      ready.outBase, ready.inBase, ?_, ready.zero, ?_, ready.one⟩
    · simpa only [RouteCall.startOffset, hoff, zero_add] using partialRun.offset
    · exact (partialRun.regs _ widthKeep).trans hwidth
  obtain ⟨d, run, result⟩ := RouteCall.run hl.successorCall v (.inl i) hW hfit q body callReady ready.resident
  exact ⟨d, run, result.pc,
    ⟨⟨fun a ha ↦ result.frame a ha.1, result.memory, result.persistent⟩,
      result.frame _ (RouteCall.preserved_reg P.reg 3 (by decide)),
      result.frame _ (RouteCall.preserved_reg P.reg 16 (by decide)), result.mask⟩⟩

theorem successors {P : Program p r} {M : Machine W p r k} (hl : P.Linked M)
    (v : Position D) (buf : Buffers D H w) (base : LocalPort → Word W) (c : Config W p r)
    (hc : c.pc = P.succ 0) (inp : Inputs P.reg v buf base c)
    (hwidth : c.reg (P.reg 21) = ((8 * w : ℕ) : Word W))
    (hoff : c.reg (P.reg 16) = 0) (hW : D < W) (hfit : 8 * w < 2 ^ W) :
    ∃ t d, t ≤ (13 * (8 * w) + 37) * D + 2 ∧ Prefix M c (List.replicate t .tick) d ∧
      d.pc = P.pc 3 ∧ d.reg (P.reg 3) = (D : Word W) ∧
      RouteRange.Partial (RangeKeep P.reg 3) (P.reg 16) (P.reg 22) (8 * w) D
        (fun i : Fin D ↦ RouteCall.Good v buf (.inl i)) c d := by
  obtain ⟨d, pre, result⟩ := successors_exact hl v buf base c hc inp hwidth hoff hW hfit
  exact ⟨_, d, succTicks_le W v H w, pre, result⟩

end PairSimulation.RouteSchedule

end VPVNP
end Computability
end OAI
