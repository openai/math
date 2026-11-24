import OAI.Computability.VPVNP.PairShrinkHiddenInputs
import OAI.Computability.VPVNP.PairShrinkHiddenCost

/-!
# A native instruction table for the shrinking hidden-field pass

Four public operands identify the packed owner, private slot base and stride,
and old-level header. The finite table first loads these operands, reads the
live published header, scans the owner's fields and enters an accepting halt.
Only the binary compiler for the two stage constants depends on the stage.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkHiddenGuess.Table

open BurstRAM PrivateRAM CompressorRecords NodeArguments.ChildScan
open scoped Fin.CommRing

variable (s t : ℕ)

/-- The compiled register-setup rows for the hidden scan's header recipe at selector width `s`
and owner row stride `t`. -/
abbrev lines := RegisterSetup.lines (Header.recipe s t)
/-- Register count of the compiled header recipe, including its ten output registers and its
expression-evaluation workspace. -/
abbrev aux := RegisterSetup.regCount (Header.recipe s t)
/-- Labels for the four public operand loads, the compiled header rows, the field-scan stages,
and the accepting halt. -/
abbrev Label := (Fin 4 ⊕ Fin (lines s t).length) ⊕ (Stage ⊕ Unit)
/-- Physical register indices for the scan's 22 registers, the header compiler's auxiliary
bank, and the six source registers. -/
abbrev Reg := Fin 22 ⊕ (Fin (aux s t) ⊕ Fin 6)
/-- Number of program counters in the reset-entry hidden-field instruction table. -/
abbrev P := Fintype.card (Label s t)
/-- Number of physical registers allocated to the reset-entry hidden-field program. -/
abbrev R := Fintype.card (Reg s t)

/-- Encode a symbolic instruction label as a program counter using the finite enumeration of
table labels. -/
def label (x : Label s t) : Fin (P s t) := Fintype.equivFin _ x
/-- Program counter for the initial load of the indexed public operand. -/
def boot (i : Fin 4) := label s t (.inl (.inl i))
/-- Program counter of a field-scan stage inside the reset-entry table. -/
def loop (j : Stage) := label s t (.inr (.inl j))
/-- Program counter of the accepting instruction reached when the owner's remaining field count
is zero. -/
def done := label s t (.inr (.inr ()))
/-- Program counter for header instruction number `i`. An index past the last header
instruction enters the first scan control. -/
def setup (i : ℕ) := if h : i < (lines s t).length then label s t (.inl (.inr ⟨i,h⟩))
  else loop s t (.inl .one)

/-- Embed the scan's 22 logical registers in the physical register bank of the table. -/
def regs : Fin 22 ↪ Fin (R s t) := Function.Embedding.inl.trans (Fintype.equivFin _).toEmbedding
/-- Physical register for each of the header recipe's six protected source positions. -/
def inputs (i : Fin 6) : Fin (R s t) := Fintype.equivFin _ (Sum.inr (Sum.inr i))

private def place {v : ℕ} (i : Fin v) : Fin 22 ⊕ (Fin v ⊕ Fin 6) :=
  if h : i.val < 10 then .inl (Header.target ⟨i.val,h⟩) else .inr (.inl i)

private theorem place_injective {v : ℕ} : Function.Injective (place (v := v)) := by
  intro i j eq
  have target : Function.Injective Header.target := by decide
  by_cases hi : i.val < 10 <;> by_cases hj : j.val < 10 <;>
    simp only [place,hi,hj, dite_true,dite_false,Sum.inl.injEq,Sum.inr.injEq,
      reduceCtorEq] at eq
  · exact Fin.ext (congrArg (fun k : Fin 10 => k.val) (target eq))
  · exact eq

/-- Embed the header compiler's registers so its ten outputs land in their designated scan
registers and its other registers use the auxiliary bank. -/
def vm : Fin (aux s t) ↪ Fin (R s t) := (⟨place,place_injective⟩ : _ ↪ _).trans
  (Fintype.equivFin _).toEmbedding

theorem safe (i : Fin (aux s t)) (j : Fin 6) : vm s t i ≠ inputs s t j := by
  intro eq
  have h : place i = .inr (.inr j) := (Fintype.equivFin _).injective eq
  unfold place at h
  split at h <;> simp at h

theorem outputs (i : Fin 10) : vm s t (RegisterSetup.output (Header.recipe s t) i) =
    regs s t (Header.target i) := by
  change Fintype.equivFin _ (place _) = Fintype.equivFin _ _
  simp [place,RegisterSetup.output,i.isLt]

/-- Assign the four public operand loads to source positions 0, 1, 2, and 5, with the old-level
header address in position 5. -/
def source : Fin 4 → Fin 6 := ![0,1,2,5]
/-- Successor of a public operand load. The first three loads advance to the next load, and the
fourth enters header setup. -/
def afterBoot (i : Fin 4) : Fin (P s t) :=
  if h : i.val+1 < 4 then boot s t ⟨i.val+1,h⟩ else setup s t 0

/-- Reset-entry instruction template that loads four public operands, executes the compiled
header recipe, scans the owner's fields, and accepts at the end. -/
def template : Template (P s t) (R s t) 4 where
  literalWidth := 3
  entry := boot s t 0
  code j := match (Fintype.equivFin (Label s t)).symm j with
    | .inl (.inl i) => .publicWord (inputs s t (source i)) i (afterBoot s t i)
    | .inl (.inr i) => RegisterSetup.instruction (vm s t) (inputs s t) ((lines s t)[i.val]) (setup s t (i.val+1))
    | .inr (.inl j) => instruction (loop s t) (regs s t) (done s t) j
    | .inr (.inr ()) => .accept

variable {W : ℕ} (pub : Fin 4 → Word W)

theorem linked : Linked ((template s t).instantiate W pub) (loop s t) (regs s t) (done s t) := by
  intro j
  simpa only [Template.instantiate,template,loop,label,Equiv.symm_apply_apply] using
    resize_instruction (k := 4) (W := W) (loop s t) (regs s t) (done s t) j

private theorem resize_setup (i : Instr 2 (P s t) (R s t) 4) : (i.resize 3).resize W = i.resize W := by
  cases i with
  | constant r v pc =>
    have fit : v.val < 8 := v.isLt.trans_le (by decide : 2^2 ≤ 2^3)
    simp [Instr.resize,Nat.mod_eq_of_lt fit]
  | _ => rfl

theorem header_linked : RegisterSetup.Linked (vm s t) (inputs s t) ((template s t).instantiate W pub)
    (setup s t) (lines s t) := by
  intro i
  simp only [Template.instantiate,template,setup,dite_eq_left i.isLt,label,Equiv.symm_apply_apply]
  rw [← RegisterSetup.resize_instruction (w := 3),resize_setup, RegisterSetup.resize_instruction]

theorem boot_code (i : Fin 4) : ((template s t).instantiate W pub).code (boot s t i) =
    .publicWord (inputs s t (source i)) i (afterBoot s t i) := by
  simp [Template.instantiate,template,boot,label,Instr.resize]

theorem done_code : ((template s t).instantiate W pub).code (done s t) = .accept := by
  simp [Template.instantiate,template,done,label,Instr.resize]

end PairSimulation.ShrinkHiddenGuess.Table

end

end VPVNP
end Computability
end OAI
