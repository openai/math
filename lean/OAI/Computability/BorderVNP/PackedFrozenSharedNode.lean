import OAI.Computability.BorderVNP.PackedFrozenOldFields
import OAI.Computability.BorderVNP.PackedFrozenNamedCarry
import OAI.Computability.BorderVNP.PackedFrozenOperands

/-! # One native node for geometry, work, clipped intervals and the complete row tape

The measured selector and checked successor are run on the same old words. The
actual histogram, earlier immutable rows and the new geometry remain accessible
to the record writers. Vacant old widths are masked once before all writers.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.Shared

open Crossing Shortening Shortening.PublicDenseReceipt Shortening.SeedIntervals Shortening.StaticRows
open DirectoryCircuit CellAddressCircuit PackedHistoryCircuit VPVNP.VerifierNetwork
open scoped Classical

/-- Source, measured old fields, returned widths and guard before masking. -/
abbrev Front (Input Measured Widths : Type) := Input ⊕ (Measured ⊕ (Widths ⊕ Unit))
/-- The whole shared assignment after computing the old-width mask. -/
abbrev Context (Input Measured Widths : Type) (rows w : ℕ) := OldFields.Pin (Front Input Measured Widths) rows w

/-- The measured old operand in the unmasked source. -/
def operand {X Y Z : Type} (y : Y) : Front X Y Z := .inr (.inl y)
/-- An original child or histogram bit in the masked shared source. -/
def input {X Y Z : Type} {rows w : ℕ} (x : X) : Context X Y Z rows w := .inl (.inl x)
/-- A selected measurement bit in the masked shared source. -/
def selected {X Y Z : Type} {rows w : ℕ} (y : Y) : Context X Y Z rows w := .inl (operand y)
/-- A returned geometry or width bit in the masked shared source. -/
def widths {X Y Z : Type} {rows w : ℕ} (z : Z) : Context X Y Z rows w := .inl (.inr (.inr (.inl z)))
/-- The bank acceptance flag emitted by the checked width and geometry pass. -/
def guard {X Y Z : Type} {rows w : ℕ} : Context X Y Z rows w := .inl (.inr (.inr (.inr ())))
/-- One of the two shared Boolean constant wires. -/
def literal {X Y Z : Type} {rows w : ℕ} (b : Bool) : Context X Y Z rows w := .inr (.inr b)

variable {D rows w : ℕ} {Input MeasuredInput A Widths : Type}
    [Fintype Input] [Fintype MeasuredInput] [Fintype Widths] (O : Operands MeasuredInput A D rows w)
    (fromGeo : MeasuredInput → Input) (next : Frame Input (Widths ⊕ Unit))

/-- Run both selected passes and keep every original histogram and child tape wire. -/
noncomputable def front : Frame Input (Front Input O.Pin Widths) :=
  (parallelFrame (O.frame.subst (Frame.initial fromGeo)) next).withInput

/-- The sole preparatory mask for old holes and the two shared literal wires. -/
noncomputable def source : Frame Input (Context Input O.Pin Widths rows w) :=
  (OldFields.frame (mapPins (operand (X := Input) (Z := Widths)) O.pop) (mapColumns operand O.col)).subst
    (front O fromGeo next)

theorem source_size : (source O fromGeo next).size ≤ O.frame.size+next.size+(rows*w+2)*3 := by
  simp only [source,front,Frame.subst_size,Frame.initial_size,zero_add,Frame.withInput_size,parallelFrame_size]
  exact Nat.add_le_add_left (OldFields.frame_size _ _) _

theorem source_input (x : Input → Bool) (z : Input) :
    (source O fromGeo next).eval x (input z) = x z := by
  simp only [source,input,Frame.subst_eval,OldFields.original,front,Frame.withInput_eval_inl]

theorem source_selected (x : Input → Bool) (z : O.Pin) :
    (source O fromGeo next).eval x (selected z) = O.frame.eval (x ∘ fromGeo) z := by
  simp only [source,selected,operand,Frame.subst_eval,OldFields.original,front,Frame.withInput_eval_inr,
    parallelFrame_eval_inl]
  exact congrArg (fun y => O.frame.eval y z) (funext fun j => Frame.initial_eval fromGeo x j)

theorem source_widths (x : Input → Bool) (z : Widths) :
    (source O fromGeo next).eval x (widths z) = next.eval x (.inl z) := by
  simp only [source,widths,Frame.subst_eval,OldFields.original,front,Frame.withInput_eval_inr,parallelFrame_eval_inr]

theorem source_guard (x : Input → Bool) :
    (source O fromGeo next).eval x guard = next.eval x (.inr ()) := by
  simp only [source,guard,Frame.subst_eval,OldFields.original,front,Frame.withInput_eval_inr,parallelFrame_eval_inr]

theorem source_literal (x : Input → Bool) (b : Bool) :
    (source O fromGeo next).eval x (literal b) = b := by
  simp only [source,literal,Frame.subst_eval,OldFields.literal]

variable {Tape : Type} [Fintype Tape] (emit : Frame (Context Input O.Pin Widths rows w) Tape)

/-- The width-augmented geometry and guard keep their checked outputs; the complete
tape is installed next to them in the very same returned node. -/
noncomputable def install : Frame Input ((Widths ⊕ Tape) ⊕ Unit) :=
  (emit.withInput.select (Sum.elim (Sum.elim (Sum.inl ∘ widths) Sum.inr) (fun _ => .inl guard))).subst
    (source O fromGeo next)

theorem install_size : (install O fromGeo next emit).size ≤
    O.frame.size+next.size+(rows*w+2)*3+emit.size := by
  simp only [install,Frame.subst_size,Frame.select_size,Frame.withInput_size]
  exact Nat.add_le_add_right (source_size O fromGeo next) _

theorem install_widths (x : Input → Bool) (z : Widths) :
    (install O fromGeo next emit).eval x (.inl (.inl z)) = next.eval x (.inl z) := by
  simp [install,source_widths]

theorem install_guard (x : Input → Bool) :
    (install O fromGeo next emit).eval x (.inr ()) = next.eval x (.inr ()) := by
  simp [install,source_guard]

theorem install_tape (x : Input → Bool) (z : Tape) :
    (install O fromGeo next emit).eval x (.inl (.inr z)) = emit.eval ((source O fromGeo next).eval x) z := by
  simp [install]

end Packing.Inherited.FrozenTape.Shared

end BorderVNP
end Computability
end OAI
