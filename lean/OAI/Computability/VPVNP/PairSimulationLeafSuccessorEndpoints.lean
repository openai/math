import OAI.Computability.VPVNP.PairSimulationLeafSuccessorCode

/-!
# Testing the endpoints of successor fields

A site sends its successor field unless it is the last site. It receives
a field unless it is site zero. The active paths enter the classifier with
the sending site's address, while the two endpoints select a zero field.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafSuccessorFields

open BurstRAM PrivateRAM CursorNetwork PrimedCounter.GuessWord
open LeafFieldCopy (word)
open scoped Fin.CommRing

variable {D W p r k : ℕ} {M : Machine W p r k} {pc : Stage → Fin p}
variable {reg : Fin 20 ↪ Fin r} {done : Fin p}

private theorem endpoint_test (link : Linked M pc reg done) (recv : Bool) (base : LocalPort → ℕ)
    (v : Fin (2^D)) (w : ℕ) (c : Config W p r) (hc : c.pc = pc (if recv then .recvTest else .sendNext))
    (fixed : Fixed reg base v w c) (hDW : D < W) :
    ∃ d, Prefix M c (List.replicate (if recv then 1 else 2) .tick) d ∧
      d.pc = pc (if active recv v then .sender recv else .zeroOffset recv) ∧
      d.reg (reg 2) = c.reg (reg 2) ∧ Frame reg c d ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  have cap : 2^D < 2^W := Nat.pow_lt_pow_right (by decide) hDW
  have vfit := v.isLt.trans cap
  cases recv with
  | false =>
    let next := c.put (pc .sendTest) (reg 17) (BinaryOp.add.eval (c.reg (reg 13)) (c.reg (reg 3)))
    have s₁ : M.program.step c = .localStep next := step_at link .sendNext c hc
    have val : (next.reg (reg 17)).val = v.val+1 := by
      have fit : v.val+1 < 2^W := lt_of_le_of_lt v.isLt cap
      simp [next, Config.put, BinaryOp.eval, fixed.site, fixed.one, word, Fin.val_add, Fin.val_natCast,
        Nat.mod_eq_of_lt vfit, Nat.mod_eq_of_lt fit, Nat.mod_eq_of_lt (by omega : 1 < 2^W)]
    have sites : (next.reg (reg 14)).val = 2^D := by
      have eq : next.reg (reg 14) = word W (2^D) := by simpa [next, Config.put] using fixed.sites
      rw [eq, Fin.val_cast_of_lt cap]
    let d := {next with pc := pc (if active false v then .sender false else .zeroOffset false)}
    have s₂ : M.program.step next = .localStep d := by
      rw [step_at link .sendTest next rfl]
      by_cases hv : v.val+1 < 2^D
      · have ne : next.reg (reg 17) ≠ next.reg (reg 14) := by
          intro he
          have := congrArg Fin.val he
          omega
        simp [instruction, Instr.run, d, active, hv, ne]
      · have he : next.reg (reg 17) = next.reg (reg 14) := Fin.ext (by have := v.isLt; omega)
        simp [instruction, Instr.run, d, active, hv, he]
    refine ⟨d, .tick s₁ (.tick s₂ (.nil _)), rfl, ?_, frame_put c _ 17 _ (by decide), rfl, rfl⟩
    simp [d, next, Config.put]
  | true =>
    let d := {c with pc := pc (if active true v then .sender true else .zeroOffset true)}
    have val : (c.reg (reg 13)).val = v.val := by
      rw [fixed.site, Fin.val_cast_of_lt vfit]
    have s₁ : M.program.step c = .localStep d := by
      rw [step_at link .recvTest c hc]
      by_cases hv : 0 < v.val
      · have ne : c.reg (reg 13) ≠ c.reg (reg 16) := by
          rw [fixed.zero]
          intro he
          rw [he] at val
          simp at val
          omega
        simp [instruction, Instr.run, d, active, hv, ne]
      · have he : c.reg (reg 13) = c.reg (reg 16) := by
          rw [fixed.zero]
          exact Fin.ext (by simpa only [Fin.val_zero] using val.trans (Nat.eq_zero_of_not_pos hv))
        simp [instruction, Instr.run, d, active, hv, he]
    exact ⟨d, .tick s₁ (.nil _), rfl, rfl, fun _ _ => rfl, rfl, rfl⟩

/-- Run the linked endpoint rows. Both paths preserve the destination cursor
in register two, every register in the frame, and all private memory. -/
theorem endpoint_run (link : Linked M pc reg done) (recv : Bool) (base : LocalPort → ℕ)
    (v : Fin (2^D)) (w : ℕ) (c : Config W p r) (hc : c.pc = pc (if recv then .recvTest else .sendNext))
    (fixed : Fixed reg base v w c) (hDW : D < W) :
    ∃ d, Prefix M c (List.replicate (if recv then 2 else 3) .tick) d ∧
      (if active recv v then d.pc = pc (.classify recv 0) ∧ (d.reg (reg 17)).val = sender recv v
       else d.pc = pc (.prepare recv none 0) ∧ d.reg (reg 6) = 0) ∧
      d.reg (reg 2) = c.reg (reg 2) ∧ Frame reg c d ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  obtain ⟨b, test, atBranch, cursor, frame, mem, state⟩ := endpoint_test link recv base v w c hc fixed hDW
  have ext {d : Config W p r} (h : M.program.step b = .localStep d) :
      Prefix M c (List.replicate (if recv then 2 else 3) .tick) d := by
    have run := test.append (.tick h (.nil _) : Prefix M b [.tick] d)
    cases recv <;> exact run
  have fb := fixed.of_frame frame
  cases use : active recv v with
  | false =>
    simp only [use, Bool.false_eq_true, ↓reduceIte] at atBranch ⊢
    let d := b.put (pc (.prepare recv none 0)) (reg 6) 0
    have hs : M.program.step b = .localStep d := step_at link (.zeroOffset recv) b atBranch
    refine ⟨d, ext hs, ⟨rfl, ?_⟩, ?_, frame.trans (frame_put b _ 6 _ (by decide)), mem, state⟩
    · simp [d, Config.put]
    · simpa [d, Config.put] using cursor
  | true =>
    simp only [use, ↓reduceIte] at atBranch ⊢
    let value := if recv then BinaryOp.sub.eval (b.reg (reg 13)) (b.reg (reg 3)) else b.reg (reg 13)
    let d := b.put (pc (.classify recv 0)) (reg 17) value
    have hs : M.program.step b = .localStep d := by
      cases recv <;> exact step_at link (.sender _) b atBranch
    have vfit := v.isLt.trans (Nat.pow_lt_pow_right (by decide : 1 < 2) hDW)
    have value_eq : value = word W (sender recv v) := by
      cases recv with
      | false => exact fb.site
      | true =>
        have hv : 0 < v.val := by simpa [active] using use
        change b.reg (reg 13) - b.reg (reg 3) = word W (v.val-1)
        rw [fb.site, fb.one, sub_eq_iff_eq_add]
        simpa only [word, Nat.cast_add, Nat.cast_one] using
          congrArg (fun n : ℕ => (n : Word W)) (Nat.sub_add_cancel hv).symm
    have hsender : sender recv v < 2^W := by cases recv <;> simp [sender] <;> omega
    refine ⟨d, ext hs, ⟨rfl, ?_⟩, ?_, frame.trans (frame_put b _ 17 _ (by decide)), mem, state⟩
    · simp [d, Config.put, value_eq, word, Fin.val_cast_of_lt hsender]
    · simpa [d, Config.put] using cursor

end PairSimulation.LeafSuccessorFields

end VPVNP
end Computability
end OAI
