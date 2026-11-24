import OAI.Computability.VPVNP.PairNodeChildSegment
import OAI.Computability.VPVNP.PairShrinkRoleHandoff

/-!
# Preparing and linking the argument stages of a nonleaf visit

A preparation block can read the locator retained in the following routine's register
bank and initialize a separate argument-reader bank. The same construction links the
child stage on both roles and the absorbed-field stage on a shrinking role.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexStagePrefix

open BurstRAM BurstRAM.PrivateRAM VertexImage NodeArguments
open scoped Fin.CommRing

variable {p r w : ℕ}

/-- Fixed instructions transferring operands to a phase before it starts. -/
structure Preparation (phase body : Segment) where
  /-- Number of instructions in the operand preparation that runs ahead of a phase and its
  continuation. -/
  count : ℕ
  /-- Entry ordinal of the setup portion of the preparation. -/
  entry : Fin count
  /-- Native instruction generator for the preparation under the supplied DFS, saved, local
  register, and continuation placements. -/
  row : ∀ {p r : ℕ}, (Fin count → Fin p) → (Fin 9 ↪ Fin r) → (Saved ↪ Fin r) →
    (Fin phase.privateRegs ↪ Fin r) → (Fin body.privateRegs ↪ Fin r) →
    Fin p → Fin count → Instr 5 p r 11

namespace Preparation

variable {phase body : Segment} (X : Preparation phase body)

/-- Total instruction count after concatenating setup, prepared phase, and continuation body. -/
abbrev size := X.count + (phase.count + body.count)
/-- Total private registers in the combined phase and continuation, with separate banks for
each. -/
abbrev registers (phase body : Segment) := body.privateRegs + phase.privateRegs

/-- Relocate a setup instruction from the initial block of the combined table to the program
address supplied by the placement function. -/
def setupPC (loc : Fin X.size → Fin p) (i : Fin X.count) := loc (i.castAdd _)

/-- Relocate an instruction of the prepared phase, adding the setup block length before
applying the program-address function. -/
def phasePC (loc : Fin X.size → Fin p) (i : Fin phase.count) :=
  loc ((i.castAdd body.count).natAdd X.count)

/-- Relocate a body instruction, adding the lengths of the setup and phase blocks before
applying the program-address function. -/
def bodyPC (loc : Fin X.size → Fin p) (i : Fin body.count) :=
  loc ((i.natAdd phase.count).natAdd X.count)

/-- Embed phase registers in the combined bank after the continuation's reserved registers. -/
def phaseRegs (phase body : Segment) (reg : Fin (registers phase body) ↪ Fin r) :
    Fin phase.privateRegs ↪ Fin r := (Fin.natAddEmb body.privateRegs).trans reg

/-- Embed continuation-body registers in the leading portion of the combined bank. -/
def bodyRegs (phase body : Segment) (reg : Fin (registers phase body) ↪ Fin r) :
    Fin body.privateRegs ↪ Fin r := (Fin.castAddEmb phase.privateRegs).trans reg

theorem disjoint (reg : Fin (registers phase body) ↪ Fin r) (i : Fin phase.privateRegs)
    (j : Fin body.privateRegs) : phaseRegs phase body reg i ≠ bodyRegs phase body reg j := by
  apply reg.injective.ne
  intro h
  have e := congrArg Fin.val h
  change body.privateRegs + i.val = j.val at e
  omega

/-- Prepare the phase's inputs, run it, and return directly into the next body. -/
def assemble : Segment where
  count := X.size
  privateRegs := registers phase body
  entry := X.entry.castAdd _
  row loc dfs saved reg done i :=
    let ps := phaseRegs phase body reg
    let bs := bodyRegs phase body reg
    Fin.addCases (motive := fun _ => Instr 5 _ _ 11)
      (X.row (X.setupPC loc) dfs saved ps bs (X.phasePC loc phase.entry))
      (fun j => Fin.addCases (motive := fun _ => Instr 5 _ _ 11)
        (phase.row (X.phasePC loc) dfs saved ps (X.bodyPC loc body.entry))
        (body.row (X.bodyPC loc) dfs saved bs done) j) i

theorem links (M : Machine w p r 11) (loc : Fin X.size → Fin p)
    (dfs : Fin 9 ↪ Fin r) (saved : Saved ↪ Fin r) (reg : Fin (registers phase body) ↪ Fin r)
    (done : Fin p) (installed : ∀ i, M.code (loc i) =
      (X.assemble.row loc dfs saved reg done i).resize w) :
    (∀ i, M.code (X.setupPC loc i) = (X.row (X.setupPC loc) dfs saved
      (phaseRegs phase body reg) (bodyRegs phase body reg)
      (X.phasePC loc phase.entry) i).resize w) ∧
    (∀ i, M.code (X.phasePC loc i) = (phase.row (X.phasePC loc) dfs saved
      (phaseRegs phase body reg) (X.bodyPC loc body.entry) i).resize w) ∧
    (∀ i, M.code (X.bodyPC loc i) = (body.row (X.bodyPC loc) dfs saved
      (bodyRegs phase body reg) done i).resize w) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
  · apply (installed _).trans
    simp only [assemble, Fin.addCases_left]
  · apply (installed _).trans
    simp only [assemble, Fin.addCases_left, Fin.addCases_right]
  · apply (installed _).trans
    simp only [assemble, Fin.addCases_right]

end Preparation

/-- The old-level child header reader receives the popped node and the old field table
head from the locator. Its ordinal bank has its own registers. -/
def childPreparation (a : ℕ) (body : Segment) (locator : Fin 14 ↪ Fin body.privateRegs) :
    Preparation (ChildCode.RegisterBank.segment a) body where
  count := 2
  entry := 0
  row pc _ _ ps bs next := VertexLevel.childHandoff pc (locator.trans bs)
    (ChildCode.RegisterBank.regs ps) next

/-- Assemble the child argument preparation and the supplied located body into one vertex
segment. -/
def withChildren (a : ℕ) (body : Segment) (locator : Fin 14 ↪ Fin body.privateRegs) :=
  (childPreparation a body locator).assemble

theorem child_rows (a : ℕ) (body : Segment) (locator : Fin 14 ↪ Fin body.privateRegs)
    (M : Machine w p r 11) (loc : Fin (withChildren a body locator).count → Fin p)
    (dfs : Fin 9 ↪ Fin r) (saved : Saved ↪ Fin r)
    (reg : Fin (withChildren a body locator).privateRegs ↪ Fin r)
    (done : Fin p) (installed : ∀ i, M.code (loc i) =
      ((withChildren a body locator).row loc dfs saved reg done i).resize w) :
    let X := childPreparation a body locator
    let ps := Preparation.phaseRegs (ChildCode.RegisterBank.segment a) body reg
    let bs := Preparation.bodyRegs (ChildCode.RegisterBank.segment a) body reg
    (∀ i, M.code (X.setupPC loc i) = VertexLevel.childHandoff (X.setupPC loc)
      (locator.trans bs) (ChildCode.RegisterBank.regs ps)
      (X.phasePC loc (ChildCode.RegisterBank.segment a).entry) i) ∧
    ChildBankInit.Linked M (ChildCode.RegisterBank.initPC (X.phasePC loc))
      (ChildCode.RegisterBank.bank ps)
      (ChildCode.headerPC (ChildCode.RegisterBank.loc (X.phasePC loc)) 0) ∧
    (∀ i, M.code (ChildCode.RegisterBank.loc (X.phasePC loc) i) =
      ChildCode.RegisterBank.instruction (ChildCode.RegisterBank.loc (X.phasePC loc))
        (ChildCode.RegisterBank.regs ps) (ChildCode.RegisterBank.bank ps)
        (X.bodyPC loc body.entry) i) ∧
    (∀ i, M.code (X.bodyPC loc i) = (body.row (X.bodyPC loc) dfs saved bs done i).resize w) := by
  let X := childPreparation a body locator
  obtain ⟨pre, phase, next⟩ := X.links M loc dfs saved reg done installed
  obtain ⟨init, rows⟩ := ChildCode.RegisterBank.segment_linked M _ dfs saved _ _ phase
  exact ⟨fun i => (pre i).trans (VertexLevel.resize_childHandoff ..), init, rows, next⟩

end PairSimulation.VertexStagePrefix

end VPVNP
end Computability
end OAI
