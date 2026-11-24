import OAI.Computability.VPVNP.PrimedCounterGuessWord
import Mathlib.Tactic.DeriveFintype

/-!
# Selecting the three resident field addresses at a cursor vertex

The two mask bits select the outgoing and incoming sides independently.
The same running offset locates the system's field in all four local buffers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RouteAddresses

open BurstRAM PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {w p r k : ℕ}

/-- Input flags, buffer bases and field offset, together with the three output addresses. -/
inductive Reg where
  | outFlag | inFlag | outBase (side : Bool) | inBase (side : Bool)
  | offset | zero | unused | used | incoming
  deriving DecidableEq, Fintype

/-- Each outgoing branch adds the offset to both starts. The incoming
branch adds it to the selected incoming start. -/
def instruction (pc : Fin 8 → Fin p) (reg : Reg ↪ Fin r) (done : Fin p) :
    Fin 8 → Instr w p r k :=
  ![.jumpEq (reg .outFlag) (reg .zero) (pc 1) (pc 3),
    .binary .add (reg .unused) (reg (.outBase true)) (reg .offset) (pc 2),
    .binary .add (reg .used) (reg (.outBase false)) (reg .offset) (pc 5),
    .binary .add (reg .unused) (reg (.outBase false)) (reg .offset) (pc 4),
    .binary .add (reg .used) (reg (.outBase true)) (reg .offset) (pc 5),
    .jumpEq (reg .inFlag) (reg .zero) (pc 6) (pc 7),
    .binary .add (reg .incoming) (reg (.inBase false)) (reg .offset) done,
    .binary .add (reg .incoming) (reg (.inBase true)) (reg .offset) done]

theorem resize_instruction (pc : Fin 8 → Fin p) (reg : Reg ↪ Fin r) (done : Fin p)
    (i : Fin 8) : (instruction (w := 1) (k := k) pc reg done i).resize w =
      instruction pc reg done i := by fin_cases i <;> rfl

/-- The machine contains the eight address-selection rows at their assigned labels. -/
def Linked (M : Machine w p r k) (pc : Fin 8 → Fin p) (reg : Reg ↪ Fin r) (done : Fin p) : Prop :=
  ∀ i, M.code (pc i) = instruction pc reg done i

/-- The outgoing and incoming side bits and the four local buffer bases at entry. -/
structure Ready (reg : Reg ↪ Fin r) (c : Config w p r) (outFlag inFlag : Bool)
    (outBase inBase : Bool → Word w) (offset : Word w) : Prop where
  outgoing : c.reg (reg .outFlag) = (outFlag.toNat : Word w)
  incoming : c.reg (reg .inFlag) = (inFlag.toNat : Word w)
  outBase : ∀ b, c.reg (reg (.outBase b)) = outBase b
  inBase : ∀ b, c.reg (reg (.inBase b)) = inBase b
  offset : c.reg (reg .offset) = offset
  zero : c.reg (reg .zero) = 0

/-- The selected field starts, return label and state preserved for the field scan. -/
structure Result (reg : Reg ↪ Fin r) (done : Fin p) (c d : Config w p r) (outFlag inFlag : Bool)
    (outBase inBase : Bool → Word w) (offset : Word w) : Prop where
  pc : d.pc = done
  unused : d.reg (reg .unused) = outBase (!outFlag) + offset
  used : d.reg (reg .used) = outBase outFlag + offset
  incoming : d.reg (reg .incoming) = inBase inFlag + offset
  frame : ∀ q, q ≠ reg .unused → q ≠ reg .used → q ≠ reg .incoming → d.reg q = c.reg q
  memory : d.privateMem = c.privateMem
  persistent : d.persistent = c.persistent

/-- Exactly five native local steps select the three absolute addresses. -/
theorem native {M : Machine w p r k} {pc : Fin 8 → Fin p} {reg : Reg ↪ Fin r} {done : Fin p}
    (hl : Linked M pc reg done) (hw : 0 < w) (c : Config w p r) (hc : c.pc = pc 0)
    {outFlag inFlag : Bool} {outBase inBase : Bool → Word w} {offset : Word w}
    (h : Ready reg c outFlag inFlag outBase inBase offset) :
    ∃ d, Prefix M c (List.replicate 5 .tick) d ∧ Result reg done c d outFlag inFlag outBase inBase offset := by
  let unusedPC : Fin 8 := if outFlag then 3 else 1
  let usedPC : Fin 8 := if outFlag then 4 else 2
  let incomingPC : Fin 8 := if inFlag then 7 else 6
  let c₁ := {c with pc := pc unusedPC}
  let c₂ := c₁.put (pc usedPC) (reg .unused) (outBase (!outFlag) + offset)
  let c₃ := c₂.put (pc 5) (reg .used) (outBase outFlag + offset)
  let c₄ := {c₃ with pc := pc incomingPC}
  let d := c₄.put done (reg .incoming) (inBase inFlag + offset)
  have step (i : Fin 8) (a : Config w p r) (ha : a.pc = pc i) :
      M.program.step a = (instruction pc reg done i).run M.publicData a := by
    change (M.code a.pc).run _ _ = _
    rw [ha, hl i]
  have s₀ : M.program.step c = .localStep c₁ := by
    rw [step 0 c hc]
    change CallAction.localStep {c with pc := if c.reg (reg .outFlag) = c.reg (reg .zero) then pc 1 else pc 3} = _
    rw [h.outgoing, h.zero]
    cases outFlag <;> simp [c₁, unusedPC, Nat.ne_of_gt hw]
  have s₁ : M.program.step c₁ = .localStep c₂ := by
    rw [step unusedPC c₁ rfl]
    cases outFlag <;> simp [unusedPC, usedPC, instruction, Instr.run, BinaryOp.eval, c₂, c₁, h.outBase, h.offset]
  have s₂ : M.program.step c₂ = .localStep c₃ := by
    rw [step usedPC c₂ rfl]
    cases outFlag <;> simp [usedPC, instruction, Instr.run, BinaryOp.eval, c₃, c₂, c₁, Config.put,
      h.outBase, h.offset]
  have s₃ : M.program.step c₃ = .localStep c₄ := by
    rw [step 5 c₃ rfl]
    change CallAction.localStep {c₃ with pc := if c₃.reg (reg .inFlag) = c₃.reg (reg .zero) then pc 6 else pc 7} = _
    cases inFlag <;> simp [c₄, incomingPC, c₃, c₂, c₁, Config.put, h.incoming, h.zero, Nat.ne_of_gt hw]
  have s₄ : M.program.step c₄ = .localStep d := by
    rw [step incomingPC c₄ rfl]
    cases inFlag <;> simp [incomingPC, instruction, Instr.run, BinaryOp.eval, d, c₄, c₃, c₂, c₁, Config.put,
      h.inBase, h.offset]
  refine ⟨d, .tick s₀ (.tick s₁ (.tick s₂ (.tick s₃ (.tick s₄ (.nil _))))), rfl, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp [d, c₄, c₃, c₂, Config.put]
  · simp [d, c₄, c₃, Config.put]
  · simp [d]
  · intro q hn hu hi
    simp [d, c₄, c₃, c₂, c₁, Config.put, Function.update_of_ne hn, Function.update_of_ne hu,
      Function.update_of_ne hi]

end PairSimulation.RouteAddresses

end VPVNP
end Computability
end OAI
