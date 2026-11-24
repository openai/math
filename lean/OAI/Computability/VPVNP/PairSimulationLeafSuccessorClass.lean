import OAI.Computability.VPVNP.PairSimulationLeafSuccessorMask
import OAI.Computability.VPVNP.PrimedCounterGuessWord

/-!
# Native successor-class selection

A nonwrapping successor flips a nonempty low-bit prefix. The six native
rows compute its XOR mask and count the halvings needed to reach one.
The sender and unit registers are preserved, including at mask one.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafSuccessorClass

open BurstRAM PrivateRAM PrimedCounter.GuessWord CursorRouting

variable {W D p r pubs : ℕ}

/-- Sender, unit, mask and class occupy registers 0, 1, 2 and 3 respectively. -/
def instruction (pc : Fin 6 → Fin p) (reg : Fin 4 ↪ Fin r) (done : Fin p) :
    Fin 6 → Instr W p r pubs :=
  ![.binary .add (reg 2) (reg 0) (reg 1) (pc 1),
    .binary .bitXor (reg 2) (reg 0) (reg 2) (pc 2),
    .constant (reg 3) 0 (pc 3),
    .jumpLt (reg 1) (reg 2) (pc 4) done,
    .binary .shiftRight (reg 2) (reg 2) (reg 1) (pc 5),
    .binary .add (reg 3) (reg 3) (reg 1) (pc 3)]

theorem resize_instruction (pc : Fin 6 → Fin p) (reg : Fin 4 ↪ Fin r) (done : Fin p) (i : Fin 6) :
    (instruction (W := 1) (pubs := pubs) pc reg done i).resize W = instruction pc reg done i := by
  fin_cases i <;> rfl

/-- The host contains the six rows that compute a nonwrapping successor's XOR mask and its
class by repeated halving. -/
def Linked (M : Machine W p r pubs) (pc : Fin 6 → Fin p) (reg : Fin 4 ↪ Fin r) (done : Fin p) :=
  ∀ i, M.code (pc i) = instruction pc reg done i

/-- Exact observable state at the continuation. Only the two output
registers may have changed, and the final mask is one. -/
structure Result (reg : Fin 4 ↪ Fin r) (done : Fin p) (index : ℕ) (c out : Config W p r) : Prop where
  pc : out.pc = done
  maskValue : (out.reg (reg 2)).val = 1
  classValue : (out.reg (reg 3)).val = index
  frame : ∀ j, j ≠ reg 2 → j ≠ reg 3 → out.reg j = c.reg j
  memory : out.privateMem = c.privateMem
  persistent : out.persistent = c.persistent

variable {M : Machine W p r pubs} {pc : Fin 6 → Fin p} {reg : Fin 4 ↪ Fin r} {done : Fin p}

private theorem step_at (link : Linked M pc reg done) (j : Fin 6) (c : Config W p r)
    (hc : c.pc = pc j) : M.program.step c = (instruction pc reg done j).run M.publicData c := by
  simp [Machine.program, hc, link j]

private theorem loop (link : Linked M pc reg done) (rem i : ℕ) (c : Config W p r)
    (hfit : i+rem < W) (hc : c.pc = pc 3) (ho : (c.reg (reg 1)).val = 1)
    (hm : (c.reg (reg 2)).val = mask rem) (hi : (c.reg (reg 3)).val = i) :
    ∃ out, Prefix M c (List.replicate (3*rem+1) .tick) out ∧ Result reg done (i+rem) c out := by
  induction rem generalizing c i with
  | zero =>
    have hn : ¬ c.reg (reg 1) < c.reg (reg 2) := by
      change ¬ (c.reg (reg 1)).val < (c.reg (reg 2)).val
      rw [ho, hm, mask_one]
      omega
    let out := {c with pc := done}
    have step : M.program.step c = .localStep out := by
      rw [step_at link 3 c hc]
      change CallAction.localStep {c with pc := if c.reg (reg 1) < c.reg (reg 2) then pc 4 else done} = _
      simp [hn, out]
    exact ⟨out, .tick step (.nil _), rfl, hm.trans mask_one, hi, fun _ _ _ => rfl, rfl, rfl⟩
  | succ j ih =>
    have test : c.reg (reg 1) < c.reg (reg 2) := by
      change (c.reg (reg 1)).val < (c.reg (reg 2)).val
      rw [ho, hm]
      exact one_lt_mask_succ j
    let c₁ := {c with pc := pc 4}
    let c₂ := c₁.put (pc 5) (reg 2) (BinaryOp.shiftRight.eval (c₁.reg (reg 2)) (c₁.reg (reg 1)))
    let c₃ := c₂.put (pc 3) (reg 3) (BinaryOp.add.eval (c₂.reg (reg 3)) (c₂.reg (reg 1)))
    have s₁ : M.program.step c = .localStep c₁ := by
      rw [step_at link 3 c hc]
      change CallAction.localStep {c with pc := if c.reg (reg 1) < c.reg (reg 2) then pc 4 else done} = _
      simp [test, c₁]
    have s₂ : M.program.step c₁ = .localStep c₂ := step_at link 4 c₁ rfl
    have s₃ : M.program.step c₂ = .localStep c₃ := step_at link 5 c₂ rfl
    have h1 : (c₃.reg (reg 1)).val = 1 := by simpa [c₃, c₂, c₁, Config.put] using ho
    have h2 : (c₃.reg (reg 2)).val = mask j := by
      simpa [c₃, c₂, c₁, Config.put] using step_shift (t := j) (W := W) (by omega) _ hm _ ho
    have h3 : (c₃.reg (reg 3)).val = i+1 := by
      have bound : i+1 < 2^W := (show i+1 < W by omega).trans Nat.lt_two_pow_self
      simp [c₃, c₂, c₁, Config.put, BinaryOp.eval, Fin.val_add, hi, ho, Nat.mod_eq_of_lt bound]
    obtain ⟨out, tail, res⟩ := ih (i+1) c₃ (by omega) rfl h1 h2 h3
    refine ⟨out, ?_, res.pc, res.maskValue, ?_, ?_, res.memory, res.persistent⟩
    · rw [show 3*(j+1)+1 = 3*j+1+1+1+1 by omega]
      exact .tick s₁ (.tick s₂ (.tick s₃ tail))
    · rw [res.classValue]; omega
    · intro x h₂ h₃
      rw [res.frame x h₂ h₃]
      simp [c₃, c₂, c₁, Config.put, Function.update_of_ne h₂, Function.update_of_ne h₃]

/-- Compute the class of the actual successor edge using an arbitrary
embedding into a native RAM table. Each successful loop iteration costs
three instructions, in addition to initialization and the last test. -/
theorem native (link : Linked M pc reg done) (c : Config W p r) (hc : c.pc = pc 0)
    (x : ℕ) (hx : x+1 < 2^D) (hD : D ≤ W)
    (hs : (c.reg (reg 0)).val = x) (ho : (c.reg (reg 1)).val = 1) :
    ∃ out, Prefix M c (List.replicate (4+3*(successorClass hx).val) .tick) out ∧
      Result reg done (successorClass hx).val c out := by
  subst x
  let a := c.put (pc 1) (reg 2) (BinaryOp.add.eval (c.reg (reg 0)) (c.reg (reg 1)))
  let b := a.put (pc 2) (reg 2) (BinaryOp.bitXor.eval (a.reg (reg 0)) (a.reg (reg 2)))
  let d := b.put (pc 3) (reg 3) 0
  have s₁ : M.program.step c = .localStep a := step_at link 0 c hc
  have s₂ : M.program.step a = .localStep b := step_at link 1 a rfl
  have s₃ : M.program.step b = .localStep d := step_at link 2 b rfl
  have hmask : (d.reg (reg 2)).val = mask (successorClass hx).val := by
    simpa [d,b,a,Config.put] using sender_xor (c.reg (reg 0)) (c.reg (reg 1)) hD hx ho
  have h1 : (d.reg (reg 1)).val = 1 := by simpa [d,b,a,Config.put] using ho
  obtain ⟨out, tail, res⟩ := loop link (successorClass hx).val 0 d
    (by have := (successorClass hx).isLt; omega) rfl h1 hmask (by simp [d,Config.put])
  refine ⟨out, ?_, res.pc, res.maskValue, by simpa using res.classValue, ?_, res.memory, res.persistent⟩
  · rw [show 4+3*(successorClass hx).val = 3*(successorClass hx).val+1+1+1+1 by omega]
    exact .tick s₁ (.tick s₂ (.tick s₃ tail))
  · intro z h₂ h₃
    rw [res.frame z h₂ h₃]
    simp [d,b,a,Config.put, Function.update_of_ne h₂, Function.update_of_ne h₃]

end PairSimulation.LeafSuccessorClass

end VPVNP
end Computability
end OAI
