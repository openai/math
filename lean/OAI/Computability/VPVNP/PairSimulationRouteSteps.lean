import OAI.Computability.VPVNP.PairSimulationRouteTiming

/-!
# Checking the sorting fields of one cursor-routing phase

Phase `a` visits its `a + 1` fields in ordinal order. Each iteration checks
the current block of resident buffer bits and advances the common offset by
the block width. The loop returns to the outer phase increment.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RouteSchedule

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord CursorRouting CursorNetwork RAMLayout
open scoped Fin.CommRing

variable {D H w W p r k : ℕ} [NeZero D]

/-- Execute the sorting steps of a phase and collect their acceptance tests in the running mask. -/
theorem steps_exact {P : Program p r} {M : Machine W p r k} (hl : P.Linked M)
    (v : Position D) (buf : Buffers D H w) (base : LocalPort → Word W) (a : Fin D)
    (c : Config W p r) (hc : c.pc = P.step 0) (inp : Inputs P.reg v buf base c)
    (hphase : c.reg (P.reg 3) = (a.val : Word W))
    (hbound : c.reg (P.reg 28) = ((a.val + 1 : ℕ) : Word W))
    (hwidth : c.reg (P.reg 21) = (blockBits H w : Word W))
    (hoff : c.reg (P.reg 16) = ((D * (8 * w) + layerCount a.val * blockBits H w : ℕ) : Word W))
    (hW : D < W) (hfit : blockBits H w < 2 ^ W) :
    ∃ d, Prefix M c (List.replicate (rowTicks W v H w a) .tick) d ∧ d.pc = P.phase 2 ∧
      d.reg (P.reg 4) = ((a.val + 1 : ℕ) : Word W) ∧
      RouteRange.Partial (RangeKeep P.reg 4) (P.reg 16) (P.reg 22) (blockBits H w) (a.val + 1)
        (fun j : Fin (a.val + 1) ↦ RouteCall.Good v buf (.inr (layer a j))) c d := by
  have widthKeep := rangeKeep_reg P.reg 4 21 (by decide) (by decide) (by decide)
  apply RouteRange.run_exact hl.steps (hl.control 5) (a.val + 1) (blockBits H w)
    (fun j ↦ RouteCall.ticks W v (.inr (layer a j)) (blockBits H w))
    ((Nat.succ_le_of_lt a.isLt).trans_lt (hW.trans Nat.lt_two_pow_self))
    (fun j ↦ RouteCall.Good v buf (.inr (layer a j))) (RangeKeep P.reg 4)
    (rangeKeep_reg P.reg 4 28 (by decide) (by decide) (by decide))
    (rangeKeep_reg P.reg 4 23 (by decide) (by decide) (by decide)) widthKeep
    (fun _ h ↦ h.2) (P.reg.injective.ne (by decide)) (P.reg.injective.ne (by decide))
    (P.reg.injective.ne (by decide)) c hc hbound inp.one hwidth
  intro i q body index partialRun
  have ready := inp.transfer (narrowFrame partialRun.toFrame (fun _ h ↦ h.1.1))
  have phase := (partialRun.regs _ (rangeKeep_reg P.reg 4 3 (by decide) (by decide)
    (by decide))).trans hphase
  have callReady : RouteCall.Ready (H := H) (w := w) P.reg v (.inr (layer a i)) base q := by
    refine ⟨⟨ready.cursor, ready.site, ready.dimension, phase, ?_⟩, ready.outBase, ready.inBase,
      ?_, ready.zero, (partialRun.regs _ widthKeep).trans hwidth, ready.one⟩
    · rintro l h
      cases h
      exact index
    · rw [partialRun.offset, hoff]
      simp [RouteCall.startOffset, layer, Layer.ordinal, Nat.add_mul, add_assoc]
  obtain ⟨d, pre, res⟩ :=
    RouteCall.run hl.layerCall v (.inr (layer a i)) hW hfit q body callReady ready.resident
  exact ⟨d, pre, res.pc,
    ⟨⟨fun x hx ↦ res.frame x hx.1, res.memory, res.persistent⟩,
      res.frame _ (RouteCall.preserved_reg P.reg 4 (by decide)),
      res.frame _ (RouteCall.preserved_reg P.reg 16 (by decide)), res.mask⟩⟩

theorem steps {P : Program p r} {M : Machine W p r k} (hl : P.Linked M)
    (v : Position D) (buf : Buffers D H w) (base : LocalPort → Word W) (a : Fin D)
    (c : Config W p r) (hc : c.pc = P.step 0) (inp : Inputs P.reg v buf base c)
    (hphase : c.reg (P.reg 3) = (a.val : Word W))
    (hbound : c.reg (P.reg 28) = ((a.val + 1 : ℕ) : Word W))
    (hwidth : c.reg (P.reg 21) = (blockBits H w : Word W))
    (hoff : c.reg (P.reg 16) = ((D * (8 * w) + layerCount a.val * blockBits H w : ℕ) : Word W))
    (hW : D < W) (hfit : blockBits H w < 2 ^ W) :
    ∃ t d, t ≤ (13 * blockBits H w + 37) * (a.val + 1) + 2 ∧
      Prefix M c (List.replicate t .tick) d ∧ d.pc = P.phase 2 ∧
      d.reg (P.reg 4) = ((a.val + 1 : ℕ) : Word W) ∧
      RouteRange.Partial (RangeKeep P.reg 4) (P.reg 16) (P.reg 22) (blockBits H w) (a.val + 1)
        (fun j : Fin (a.val + 1) ↦ RouteCall.Good v buf (.inr (layer a j))) c d := by
  obtain ⟨d, pre, result⟩ := steps_exact hl v buf base a c hc inp hphase hbound hwidth hoff hW hfit
  exact ⟨_, d, rowTicks_le W v H w a, pre, result⟩

end PairSimulation.RouteSchedule

end VPVNP
end Computability
end OAI
