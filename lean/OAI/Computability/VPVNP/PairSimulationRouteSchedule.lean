import OAI.Computability.VPVNP.PairSimulationRouteCall
import OAI.Computability.VPVNP.PairSimulationRouteRange

/-!
# Control tables for the cursor routing checker

The machine first visits the successor classes in order. Then it visits
each sorting phase and its steps in triangular order, advancing the same
bit offset after each field. The program text is independent of all four
buffer lengths and the number of systems.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RouteSchedule

open BurstRAM BurstRAM.PrivateRAM CursorRouting CursorNetwork RAMLayout
open scoped Fin.CommRing

variable {D H w W p r k : ℕ}

/-- Labels of a copy of the fixed three-part field checker. -/
structure CallLabels (p : ℕ) where
  /-- Geometry calculation. -/
  geom : Fin 30 → Fin p
  /-- Selection of the three addresses. -/
  addr : Fin 8 → Fin p
  /-- The field-bit scan. -/
  field : Fin 15 → Fin p

/-- The outer cursor checker has three counted loops and two copies of a
field call, which return to the appropriate loop increment. -/
structure Program (p r : ℕ) where
  /-- Routing register bank. -/
  reg : Fin 32 ↪ Fin r
  /-- Initialization, transition, offset updates and final dispatch. -/
  pc : Fin 7 → Fin p
  /-- Successor class counter. -/
  succ : Fin 3 → Fin p
  /-- Sorting phase counter. -/
  phase : Fin 3 → Fin p
  /-- Sorting step counter. -/
  step : Fin 3 → Fin p
  /-- The successor field call. -/
  sCall : CallLabels p
  /-- The sorting field call. -/
  lCall : CallLabels p
  /-- All four input buffers pass the routing checks. -/
  yes : Fin p
  /-- At least one routing check fails. -/
  no : Fin p

variable (P : Program p r)

/-- Seven scheduler instructions. Register 28 is the current sorting step
bound, and register 29 supplies the fixed sorting block width. -/
def Program.instruction : Fin 7 → Instr W p r k :=
  ![.constant (P.reg 22) 0 (P.pc 1), .constant (P.reg 16) 0 (P.succ 0),
    .binary .add (P.reg 16) (P.reg 16) (P.reg 21) (P.succ 2),
    .copy (P.reg 21) (P.reg 29) (P.phase 0),
    .binary .add (P.reg 28) (P.reg 3) (P.reg 23) (P.step 0),
    .binary .add (P.reg 16) (P.reg 16) (P.reg 21) (P.step 2),
    .jumpEq (P.reg 22) (P.reg 17) P.yes P.no]

theorem Program.resize_instruction (i : Fin 7) :
    (P.instruction (W := 1) (k := k) i).resize W = P.instruction i := by
  fin_cases i <;> rfl

/-- Every link from a loop into a field call and back is fixed once. -/
structure Program.Linked (M : Machine W p r k) : Prop where
  control : ∀ i, M.code (P.pc i) = P.instruction i
  successors : RouteLoop.Linked M P.succ (P.reg 3) (P.reg 2) (P.reg 23) (P.sCall.geom 0) (P.pc 3)
  phases : RouteLoop.Linked M P.phase (P.reg 3) (P.reg 2) (P.reg 23) (P.pc 4) (P.pc 6)
  steps : RouteLoop.Linked M P.step (P.reg 4) (P.reg 28) (P.reg 23) (P.lCall.geom 14) (P.phase 2)
  successorCall : RouteCall.Linked M P.sCall.geom P.sCall.addr P.sCall.field P.reg (P.pc 2)
  layerCall : RouteCall.Linked M P.lCall.geom P.lCall.addr P.lCall.field P.reg (P.pc 5)

/-- A one-dimensional field scan may write the index, the offset and the
field-call scratch registers. -/
def RangeKeep (reg : Fin 32 ↪ Fin r) (idx : Fin 32) (a : Fin r) : Prop :=
  RouteCall.Preserved reg a ∧ a ≠ reg idx ∧ a ≠ reg 16

/-- A sorting phase adds the outer index and step bound to the writable registers. -/
def PhaseKeep (reg : Fin 32 ↪ Fin r) (a : Fin r) : Prop :=
  RangeKeep reg 4 a ∧ a ≠ reg 3 ∧ a ≠ reg 28

/-- The whole program additionally switches the field width between passes. -/
def Keep (reg : Fin 32 ↪ Fin r) (a : Fin r) : Prop :=
  PhaseKeep reg a ∧ a ≠ reg 21

theorem rangeKeep_reg (reg : Fin 32 ↪ Fin r) (idx j : Fin 32) (h : ¬ RouteCall.Scratch j)
    (hi : j ≠ idx) (ho : j ≠ 16) : RangeKeep reg idx (reg j) :=
  ⟨RouteCall.preserved_reg reg j h, reg.injective.ne hi, reg.injective.ne ho⟩

theorem keep_reg (reg : Fin 32 ↪ Fin r) (j : Fin 32) (h : ¬ RouteCall.Scratch j)
    (h₄ : j ≠ 4) (h₁₆ : j ≠ 16) (h₃ : j ≠ 3) (h₂₈ : j ≠ 28) (h₂₁ : j ≠ 21) :
    Keep reg (reg j) :=
  ⟨⟨rangeKeep_reg reg _ _ h h₄ h₁₆, reg.injective.ne h₃, reg.injective.ne h₂₈⟩,
    reg.injective.ne h₂₁⟩

/-- Restrict a register frame to a subset of its preserved registers. -/
theorem narrowFrame {keep₁ keep₂ : Fin r → Prop} {c d : Config W p r}
    (f : RouteRange.Frame keep₁ c d) (h : ∀ a, keep₂ a → keep₁ a) : RouteRange.Frame keep₂ c d :=
  ⟨fun a ha ↦ f.regs a (h a ha), f.memory, f.persistent⟩

theorem keep_successor {a : Fin r} (h : Keep P.reg a) : RangeKeep P.reg 3 a :=
  ⟨h.1.1.1,h.1.2.1,h.1.1.2.2⟩

/-- Fixed inputs supplied by the leaf expansion. The original four buffers
occupy private words and may have arbitrary contents. -/
structure Inputs (reg : Fin 32 ↪ Fin r) (v : Position D) (buf : Buffers D H w)
    (base : LocalPort → Word W) (c : Config W p r) : Prop where
  cursor : c.reg (reg 0) = (v.1.val : Word W)
  site : c.reg (reg 1) = (v.2.val : Word W)
  dimension : c.reg (reg 2) = (D : Word W)
  outBase : ∀ b, c.reg (reg (RouteCall.outSlot b)) = base (.outgoing b)
  inBase : ∀ b, c.reg (reg (RouteCall.inSlot b)) = base (.incoming b)
  zero : c.reg (reg 17) = 0
  one : c.reg (reg 23) = 1
  sortWidth : c.reg (reg 29) = (blockBits H w : Word W)
  resident : RouteCall.Resident c base buf

theorem Inputs.transfer {reg : Fin 32 ↪ Fin r} {v : Position D} {buf : Buffers D H w}
    {base : LocalPort → Word W} {c d : Config W p r} (h : Inputs reg v buf base c)
    (f : RouteRange.Frame (Keep reg) c d) : Inputs reg v buf base d := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (f.regs _ (keep_reg reg 0 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))).trans h.cursor
  · exact (f.regs _ (keep_reg reg 1 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))).trans h.site
  · exact (f.regs _ (keep_reg reg 2 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))).trans h.dimension
  · intro b
    apply Eq.trans (f.regs _ ?_) (h.outBase b)
    cases b <;> apply keep_reg <;> decide
  · intro b
    apply Eq.trans (f.regs _ ?_) (h.inBase b)
    cases b <;> apply keep_reg <;> decide
  · exact (f.regs _ (keep_reg reg 17 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))).trans h.zero
  · exact (f.regs _ (keep_reg reg 23 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))).trans h.one
  · exact (f.regs _ (keep_reg reg 29 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))).trans h.sortWidth
  · intro port j
    rw [f.memory]
    exact h.resident port j

/-- A sorting step with its phase and zero-based step counter. -/
def layer (phase : Fin D) (step : Fin (phase.val + 1)) : Layer D :=
  ⟨phase.val, step.val, phase.isLt, Nat.le_of_lt_succ step.isLt⟩

end PairSimulation.RouteSchedule

end VPVNP
end Computability
end OAI
