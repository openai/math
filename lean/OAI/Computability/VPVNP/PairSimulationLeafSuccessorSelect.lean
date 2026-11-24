import OAI.Computability.VPVNP.PairSimulationLeafSuccessorCode

/-!
# Choosing the source arc and offset for an active successor field
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafSuccessorFields

open BurstRAM PrivateRAM CursorNetwork CursorRouting PrimedCounter.GuessWord
open LeafFieldCopy (word)
open scoped Fin.CommRing

variable {W D w p r k : ℕ} {M : Machine W p r k} {pc : Stage → Fin p} {reg : Fin 20 ↪ Fin r} {done : Fin p}

theorem classify_run (link : Linked M pc reg done) (recv : Bool) (base : LocalPort → ℕ)
    (v : Fin (2^D)) (c : Config W p r) (hc : c.pc = pc (.classify recv 0))
    (hf : Fixed reg base v w c) (hDW : D < W) (hactive : active recv v = true)
    (hsender : (c.reg (reg 17)).val = sender recv v) :
    let j := successorClass (sender_lt recv v hactive)
    ∃ out, Prefix M c (List.replicate (5+3*j.val+(if recv then 1 else 0)) .tick) out ∧
      out.pc = pc (.prepare recv (some (useSide recv j)) 0) ∧
      out.reg (reg 6) = word W (j.val*(8*w)) ∧ out.reg (reg 2) = c.reg (reg 2) ∧
      Frame reg c out ∧ out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  let j := successorClass (sender_lt recv v hactive)
  have hl : LeafSuccessorClass.Linked M (pc ∘ Stage.classify recv) (classRegs reg) (pc (.offset recv)) :=
    fun i => link (.classify recv i)
  have hone : (c.reg (classRegs reg 1)).val = 1 := by
    change (c.reg (reg 3)).val = 1
    rw [hf.one]
    exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  obtain ⟨a, pa, ra⟩ := LeafSuccessorClass.native hl c hc (sender recv v) (sender_lt recv v hactive)
    hDW.le hsender hone
  have fa : Frame reg c a :=
    fun z hz => ra.frame z (hz 18 (by decide)) (hz 19 (by decide))
  have fixed := hf.of_frame fa
  have cur : a.reg (reg 2) = c.reg (reg 2) :=
    ra.frame _ (reg.injective.ne (by decide : (2 : Fin 20) ≠ 18))
      (reg.injective.ne (by decide : (2 : Fin 20) ≠ 19))
  have hfit : j.val < 2^W := (j.isLt.trans hDW).trans Nat.lt_two_pow_self
  have hj : a.reg (reg 19) = word W j.val := by
    apply Fin.ext
    exact ra.classValue.trans (Nat.mod_eq_of_lt hfit).symm
  let b := a.put (pc (if recv then .side else .prepare false (some true) 0)) (reg 6) (word W (j.val*(8*w)))
  have step : M.program.step a = .localStep b := by
    rw [step_at link _ a ra.pc]
    simp [instruction, Instr.run, BinaryOp.eval, hj, fixed.len, b, word]
  have fb : Frame reg a b := frame_put _ _ _ _ (by decide)
  have cur' : b.reg (reg 2) = c.reg (reg 2) := by simpa [b, Config.put] using cur
  dsimp only
  cases recv with
  | false =>
    refine ⟨b, ?_, rfl, by simp [b, Config.put, j], cur', fa.trans fb, ra.memory, ra.persistent⟩
    have h := pa.append (Prefix.tick step (.nil b))
    change Prefix M c (List.replicate (5+3*j.val+0) .tick) b
    change Prefix M c (List.replicate (4+3*j.val) .tick ++ List.replicate 1 .tick) b at h
    rwa [← List.replicate_add, show 4+3*j.val+1 = 5+3*j.val+0 by omega] at h
  | true =>
    let dest := pc (.prepare true (some (useSide true j)) 0)
    let out := {b with pc := dest}
    have hlast : D-1 < 2^W := (show D-1 < W by omega).trans Nat.lt_two_pow_self
    have eq : b.reg (reg 19) = b.reg (reg 12) ↔ j.val = D-1 := by
      simp only [b, Config.put, Function.update_of_ne (reg.injective.ne (by decide : (19 : Fin 20) ≠ 6)),
        Function.update_of_ne (reg.injective.ne (by decide : (12 : Fin 20) ≠ 6)), hj, fixed.last]
      constructor
      · intro h
        have e := congrArg Fin.val h
        change j.val % 2^W = (D-1)%2^W at e
        rwa [Nat.mod_eq_of_lt hfit, Nat.mod_eq_of_lt hlast] at e
      · rintro h; rw [h]
    have sside : M.program.step b = .localStep out := by
      rw [step_at link .side b rfl]
      simp only [instruction, Instr.run, eq, out, dest, useSide, ite_true]
      split <;> simp_all
    refine ⟨out, ?_, rfl, by simp [out, b, Config.put, j], cur', fa.trans fb, ra.memory, ra.persistent⟩
    have h := pa.append (Prefix.tick step (.tick sside (.nil out)))
    change Prefix M c (List.replicate (5+3*j.val+1) .tick) out
    change Prefix M c (List.replicate (4+3*j.val) .tick ++ List.replicate 2 .tick) out at h
    rwa [← List.replicate_add, show 4+3*j.val+2 = 5+3*j.val+1 by omega] at h

end PairSimulation.LeafSuccessorFields

end VPVNP
end Computability
end OAI
