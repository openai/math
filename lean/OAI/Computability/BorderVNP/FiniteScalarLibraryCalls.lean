import OAI.Computability.BorderVNP.FiniteScalarLibrary

/-! # Two real private opcodes in the finite-field team

The compact signed validator stays at its original identifiers. Identifier one
runs the bit-major field reader on one tape of the same architecture. It gives a
positive signed RAM return and supplies the genuine field value to the weighted
processor when its actual count word burst is valid.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteScalarLibrary

open TeamSite TeamPrivateTape TeamPrivateValue VPVNP.BurstRAM
open scoped Classical

/-- Number of binary tracks for blank, zero, and one on a native tape. -/
abbrev AlphabetWidth := Fintype.card (Option Bool)
variable {Q : Type} {m w d : ℕ} (F : Type*) [Field F] [Fintype F]
/-- The finite control labels of both installed kinds of private routine. -/
abbrev Control (Q : Type) (F : Type*) [Fintype F] := Q ⊕ FiniteScalarRounds.Phase (Fintype.card F)

/-- Widen the scalar routine to the cell's existing tape count and symbol width. -/
noncomputable def scalarMacro (tape : Fin m) : Macro (Control Q F) (Option Bool) m AlphabetWidth :=
  let M := FiniteScalarRounds.routine F
  ⟨M.alphabet,M.digit,tape,rightTable tape M.table,.inr M.start⟩

/-- Overlay the scalar routine at identifier one without changing any existing
cell validation or administrative routine at the other identifiers. -/
noncomputable def combine (lib : Fin 8 → Macro Q (Option Bool) m AlphabetWidth) :
    Fin 8 → Macro (Control Q F) (Option Bool) m AlphabetWidth :=
  fun i => if i=1 then scalarMacro F (lib i).inputTape else leftMacro (lib i)

/-- The installed field terminals on the exact same combined library. -/
noncomputable def returns (lib : Fin 8 → Macro Q (Option Bool) m AlphabetWidth)
    (old : FieldProcessor.Returns Q (Option Bool) F m 8) :
    FieldProcessor.Returns (Control Q F) (Option Bool) F m 8 :=
  fun i => if i=1 then rightReturn (lib i).inputTape (FiniteScalarRounds.result F) else leftReturn (old i)

/-- A call at any original signed opcode retains its old RAM result. -/
theorem original_eval (lib : Fin 8 → Macro Q (Option Bool) m AlphabetWidth) (j : Fin 8) (hj : j ≠ 1)
    (fuel : ℕ) (vs : List (Word w)) (choices : List Bool) :
    (combine F lib j).eval fuel vs choices = (lib j).eval fuel vs choices := by
  rw [combine,ite_eq_right hj,left_eval_eq]

/-- All non-scalar routine cutoffs still use the original native clock. -/
theorem original_bounded (lib : Fin 8 → Macro Q (Option Bool) m AlphabetWidth) (j : Fin 8) (hj : j ≠ 1)
    (fuel : ℕ) (vs : List (Word w)) :
    (combine F lib j).bounded fuel vs ↔ (lib j).bounded fuel vs := by
  rw [combine,ite_eq_right hj]
  exact left_bounded ..

private theorem one_input (tape : Fin m) (bs : List Bool) :
    (fun _ : Fin 1 => input none some tape bs tape) = input none some (0 : Fin 1) bs := by
  funext i
  have hi : i=0 := Subsingleton.elim ..
  simp [input,hi]

/-- The added private opcode halts within one native tick per available input bit. -/
theorem scalar_bounded (lib : Fin 8 → Macro Q (Option Bool) m AlphabetWidth)
    (fuel : ℕ) (vs : List (Word w)) (fits : vs.length*w < fuel) :
    (combine F lib 1).bounded fuel vs := by
  rw [combine,ite_eq_left rfl]
  unfold Macro.bounded scalarMacro
  rw [right_bounded]
  change TapeStops (FiniteScalarRounds.table F) none fuel _ (fun _ => input none some (lib 1).inputTape (TeamPrivateCall.inputBits vs) (lib 1).inputTape)
  rw [one_input]
  exact FiniteScalarRounds.bounded F vs fuel fits

/-- The field return of the actual combined opcode reads precisely the word
array produced by the existing compact writer. -/
theorem scalar_return (lib : Fin 8 → Macro Q (Option Bool) m AlphabetWidth)
    (old : FieldProcessor.Returns Q (Option Bool) F m 8)
    (c : FiniteScalarRounds.Index F → Fin d → Bool) (hw : 0<w) (event : TeamRAM.Event w) (fuel : ℕ)
    (words : event.old = RoutingISA.CompactFrame.pack w (FiniteScalarRounds.stream F c))
    (fits : 2*d*Fintype.card F < fuel) :
    FieldProcessor.returned (combine F lib 1) (returns F lib old 1) fuel event =
      if event.choices.isEmpty then some (∏ i, (Fintype.equivFin F).symm i ^ FieldPowers.digits (List.ofFn (c i))) else none := by
  simp only [combine,returns,ite_true,scalarMacro,FieldProcessor.returned,right_value]
  change FieldSelect.nativeReturn (FiniteScalarRounds.table F) none (FiniteScalarRounds.result F) fuel _
    (fun _ => input none some (lib 1).inputTape (TeamPrivateCall.inputBits event.old) (lib 1).inputTape) event.choices = _
  rw [one_input]
  exact FiniteScalarRounds.event_value F hw c event fuel words fits

/-- Non-scalar field outputs, even outside the prime field, are left unchanged. -/
theorem original_return (lib : Fin 8 → Macro Q (Option Bool) m AlphabetWidth)
    (old : FieldProcessor.Returns Q (Option Bool) F m 8) (j : Fin 8) (hj : j≠1) (fuel : ℕ) (event : TeamRAM.Event w) :
    FieldProcessor.returned (combine F lib j) (returns F lib old j) fuel event =
      FieldProcessor.returned (lib j) (old j) fuel event := by
  simp only [combine,returns,hj,ite_false,FieldProcessor.returned,leftMacro,left_value]

end FiniteScalarLibrary

end BorderVNP
end Computability
end OAI
