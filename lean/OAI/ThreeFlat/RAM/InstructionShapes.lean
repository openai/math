import OAI.ThreeFlat.RAM.ProgramEncoding
import Mathlib.Data.Fintype.Prod

namespace OAI
/-! # A polynomial enumeration of zero-width instruction shapes

A zero-width instruction retains its register, counter and public-data indices.
The only literal of width zero is used as a placeholder for the fetched word.
-/

namespace ThreeFlat.RAM.InstructionShapes

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM

private abbrev Row (b : ℕ) := Fin 15 × Fin b × Fin b × Fin b × Fin b × Fin b

private def asRow {b : ℕ} (x : Row b) : InstructionRow :=
  ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2⟩

private def readShape (p r k : ℕ) (x : Row (p+r+k+10)) : Instr 0 p r k :=
  (decodeRow 0 p r k (asRow x)).getD .reject

/-- Each shape occurs once; the enumeration depends only on the text dimensions. -/
noncomputable def all (p r k : ℕ) : List (Instr 0 p r k) :=
  (Finset.univ.image (readShape p r k)).toList

theorem all_nodup (p r k : ℕ) : (all p r k).Nodup :=
  Finset.nodup_toList _

private theorem canonical_bounds {p r k : ℕ} (i : Instr 0 p r k) :
    let s := instructionRow i
    s.tag < 15 ∧ s.a < p+r+k+10 ∧ s.b < p+r+k+10 ∧
      s.c < p+r+k+10 ∧ s.d < p+r+k+10 ∧ s.e < p+r+k+10 := by
  have opLt (op : BinaryOp) : opNumber op < 10 := by cases op <;> decide
  cases i <;> simp only [instructionRow] <;>
    (repeat' apply And.intro) <;> first | omega | exact Nat.lt_of_lt_of_le (opLt _) (by omega)

theorem mem_all {p r k : ℕ} (i : Instr 0 p r k) : i ∈ all p r k := by
  obtain ⟨ht,ha,hb,hc,hd,he⟩ := canonical_bounds i
  let x : Row (p+r+k+10) :=
    (⟨_,ht⟩, ⟨_,ha⟩, ⟨_,hb⟩, ⟨_,hc⟩, ⟨_,hd⟩, ⟨_,he⟩)
  have hx : asRow x = instructionRow i := rfl
  simp only [all, Finset.mem_toList, Finset.mem_image]
  exact ⟨x, Finset.mem_univ _, by simp [readShape,hx]⟩

theorem all_length_le (p r k : ℕ) : (all p r k).length ≤ 15 * (p+r+k+10)^5 := by
  classical
  unfold all
  rw [Finset.length_toList]
  refine (Finset.card_image_le).trans_eq ?_
  simp [Row, pow_succ, Nat.mul_assoc]

end ThreeFlat.RAM.InstructionShapes

end OAI
