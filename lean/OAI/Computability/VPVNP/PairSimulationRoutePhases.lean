import OAI.Computability.VPVNP.PairSimulationRouteSteps

/-!
# The triangular sorting-phase traversal

The outer counter supplies the phase to the step scan. Its step bound is
phase plus one, so the offset after each phase is the start of the next
triangular layer block. Every layer's routing check enters the final mask.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RouteSchedule

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord CursorRouting CursorNetwork RAMLayout
open scoped Fin.CommRing

variable {D H w W p r k : ℕ} [NeZero D]

/-- Prefix invariant after a given number of complete sorting phases. -/
structure PhaseState (reg : Fin 32 ↪ Fin r) (v : Position D) (buf : Buffers D H w)
    (width i : ℕ) (c d : Config W p r) : Prop extends RouteRange.Frame (PhaseKeep reg) c d where
  offset : d.reg (reg 16) = c.reg (reg 16) + ((layerCount i * width : ℕ) : Word W)
  maskEq : d.reg (reg 22) = 0 ↔ c.reg (reg 22) = 0 ∧
    ∀ l : Layer D, l.phase < i → RouteCall.Good v buf (.inr l)

open private layerCount_succ from OAI.Computability.VPVNP.RAMLayout

/-- Run all sorting fields using the same fixed phase and step control code
at every input size. The clock counts every visit on malformed inputs. -/
theorem phases_exact {P : Program p r} {M : Machine W p r k} (hl : P.Linked M)
    (v : Position D) (buf : Buffers D H w) (base : LocalPort → Word W) (c : Config W p r)
    (hc : c.pc = P.phase 0) (inp : Inputs P.reg v buf base c)
    (hwidth : c.reg (P.reg 21) = (blockBits H w : Word W))
    (hoff : c.reg (P.reg 16) = ((D * (8 * w) : ℕ) : Word W))
    (hW : D < W) (hfit : blockBits H w < 2 ^ W) :
    ∃ d, Prefix M c (List.replicate (phaseTicks W v H w) .tick) d ∧ d.pc = P.pc 6 ∧
      d.reg (P.reg 3) = (D : Word W) ∧ PhaseState P.reg v buf (blockBits H w) D c d := by
  let bw := blockBits H w
  let I i d := PhaseState P.reg v buf bw i c d
  have stable (j : Fin 32) (hs : ¬ RouteCall.Scratch j) (h₄ : j ≠ 4)
      (h₁₆ : j ≠ 16) (h₃ : j ≠ 3) (h₂₈ : j ≠ 28) :
      PhaseKeep P.reg (P.reg j) :=
    ⟨rangeKeep_reg P.reg 4 j hs h₄ h₁₆, P.reg.injective.ne h₃, P.reg.injective.ne h₂₈⟩
  have init : I 0 (c.put (P.phase 1) (P.reg 3) 0) := by
    refine ⟨(RouteRange.Frame.refl c).put _ _ _ (fun _ h ↦ h.2.1), ?_, ?_⟩
    · simp [layerCount, Config.put]
    · simp [Config.put]
  have visit (i : Fin D) (q : Config W p r) (hpc : q.pc = P.pc 4)
      (hidx : q.reg (P.reg 3) = (i.val : Word W)) (hI : I i.val q) :
      ∃ d, Prefix M q (List.replicate (rowTicks W v H w i + 1) .tick) d ∧
        d.pc = P.phase 2 ∧ d.reg (P.reg 3) = (i.val : Word W) ∧ d.reg (P.reg 23) = 1 ∧
        I (i.val+1) (d.put (P.phase 1) (P.reg 3) ((i.val+1 : ℕ) : Word W)) := by
    let start := q.put (P.step 0) (P.reg 28) ((i.val+1 : ℕ) : Word W)
    have fstart : RouteRange.Frame (PhaseKeep P.reg) c start :=
      hI.toFrame.put _ _ _ fun _ h ↦ h.2.2
    have inStart := inp.transfer (narrowFrame fstart fun _ h ↦ h.1)
    have hone := (hI.regs _ (stable 23 (by decide) (by decide) (by decide)
      (by decide) (by decide))).trans inp.one
    have first : M.program.step q = .localStep start := by
      change (M.code q.pc).run M.publicData q = _
      rw [hpc, hl.control 4]
      change CallAction.localStep (q.put (P.step 0) (P.reg 28)
        (q.reg (P.reg 3) + q.reg (P.reg 23))) = _
      simp [start, hidx, hone]
    have hi : start.reg (P.reg 3) = (i.val : Word W) := by simp [start, Config.put, hidx]
    have hwb : start.reg (P.reg 21) = (blockBits H w : Word W) :=
      (fstart.regs _ (stable 21 (by decide) (by decide) (by decide)
        (by decide) (by decide))).trans hwidth
    have ho : start.reg (P.reg 16) = ((D*(8*w)+layerCount i.val*bw : ℕ) : Word W) := by
      simp [start, Config.put, hI.offset, hoff, bw]
    obtain ⟨d, scan, hd, _, hscan⟩ := steps_exact hl v buf base i start rfl inStart hi
      (by simp [start]) hwb ho hW hfit
    have g := fstart.trans (narrowFrame hscan.toFrame (keep₂ := PhaseKeep P.reg) fun _ h ↦ h.1)
    have dphase : d.reg (P.reg 3) = (i.val : Word W) :=
      (hscan.regs _ (rangeKeep_reg P.reg 4 3 (by decide) (by decide) (by decide))).trans hi
    refine ⟨d, ?_, hd, dphase, (g.regs _ (stable 23 (by decide) (by decide)
      (by decide) (by decide) (by decide))).trans inp.one, ?_⟩
    · rw [Nat.add_comm (rowTicks W v H w i) 1, List.replicate_add]
      exact (Prefix.tick first (.nil _)).append scan
    refine ⟨g.put _ _ _ (fun _ h ↦ h.2.1), ?_, ?_⟩
    · change Function.update d.reg (P.reg 3) _ (P.reg 16) = _
      rw [Function.update_of_ne (P.reg.injective.ne (by decide)), hscan.offset]
      change Function.update q.reg (P.reg 28) _ (P.reg 16) + _ = _
      rw [Function.update_of_ne (P.reg.injective.ne (by decide)), hI.offset, layerCount_succ]
      simp [bw, Nat.add_mul, add_assoc]
    · change Function.update d.reg (P.reg 3) _ (P.reg 22) = 0 ↔ _
      rw [Function.update_of_ne (P.reg.injective.ne (by decide)), hscan.maskEq]
      change (Function.update q.reg (P.reg 28) _ (P.reg 22) = 0 ∧ _) ↔ _
      rw [Function.update_of_ne (P.reg.injective.ne (by decide)), hI.maskEq]
      constructor
      · rintro ⟨⟨hz, before⟩, row⟩
        refine ⟨hz, fun l hlayer ↦ ?_⟩
        by_cases he : l.phase = i.val
        · let j : Fin (i.val+1) := ⟨l.step, by have := l.step_le; omega⟩
          have eq : layer i j = l := Layer.ext he.symm rfl
          exact eq ▸ row j j.isLt
        · exact before l (by omega)
      · rintro ⟨hz, before⟩
        exact ⟨⟨hz, fun l h ↦ before l (by omega)⟩, fun j _ ↦ before (layer i j) (by simp [layer])⟩
  have hd : D < 2 ^ W := hW.trans (Nat.lt_two_pow_self)
  exact RouteLoop.run_exact hl.phases D (fun i ↦ rowTicks W v H w i + 1) hd I
    (fun _ _ h ↦ (h.regs _ (stable 2 (by decide) (by decide) (by decide)
      (by decide) (by decide))).trans inp.dimension)
    (fun _ _ _ h ↦ ⟨⟨h.regs, h.memory, h.persistent⟩, h.offset, h.maskEq⟩)
    visit c hc init

/-- The sorting traversal is bounded by the same clock on all inputs. -/
theorem phases {P : Program p r} {M : Machine W p r k} (hl : P.Linked M)
    (v : Position D) (buf : Buffers D H w) (base : LocalPort → Word W) (c : Config W p r)
    (hc : c.pc = P.phase 0) (inp : Inputs P.reg v buf base c)
    (hwidth : c.reg (P.reg 21) = (blockBits H w : Word W))
    (hoff : c.reg (P.reg 16) = ((D * (8 * w) : ℕ) : Word W))
    (hW : D < W) (hfit : blockBits H w < 2 ^ W) :
    ∃ ticks d, ticks ≤ ((13 * blockBits H w + 37)*D + 5)*D + 2 ∧
      Prefix M c (List.replicate ticks .tick) d ∧ d.pc = P.pc 6 ∧
      d.reg (P.reg 3) = (D : Word W) ∧ PhaseState P.reg v buf (blockBits H w) D c d := by
  obtain ⟨d, pre, hp, hi, st⟩ := phases_exact hl v buf base c hc inp hwidth hoff hW hfit
  exact ⟨_, d, phaseTicks_le W v H w, pre, hp, hi, st⟩

end PairSimulation.RouteSchedule

end VPVNP
end Computability
end OAI
