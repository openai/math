import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxNumbering
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxTransition
import OAI.Computability.NearSquareRoot.ScheduleGeneratorStackRows

/-! # Decoding a packed compiler row into its named-stack input -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Pack

open IntegerMultiplication CommonAlphabet Generator.SyntaxAddress Transition

variable {A : Type} [Fintype A]

def letter (a : Numbering A) : A ↪ ℕ :=
  ⟨fun v => (a.equiv v).val, (Fin.val_injective).comp a.equiv.injective⟩

noncomputable def symbols (a : Numbering A) (U : List (Prog.Loc A)) : Numbering (Prog.Sym U) :=
  a.sum (ptrNumbering (letter a) U)

def «stacks» (U : List (Prog.Loc A)) : Numbering (Prog.Ix U) :=
  (idxNumbering U).option

noncomputable def pcs (a : Numbering A) (U : List (Prog.Loc A)) : Numbering (Prog.Pc U) :=
  (ptrNumbering (letter a) U).option

def decodePC (sites : List Site) (n : ℕ) : Option Site :=
  if n = 0 then none else read sites (n-1)

def decodeTop (aSize : ℕ) (sites : List Site) (n : ℕ) : Option Symbol :=
  if n = 0 then none
  else if n-1 < aSize then some (.inl (n-1))
  else (read sites (n-1-aSize)).map Sum.inr

/-- Convert the sparse source-register name to its position in a packed tuple. -/
def slot (names : List ℕ) (i : ℕ) : ℕ :=
  if i = 0 then 0 else rank names (i-1) + 1

def heads (aSize : ℕ) (sites : List Site) (packed : ℕ) : Heads :=
  let names := registerNames sites
  let base := aSize + size sites + 1
  (List.range (names.foldr max 0 + 2)).map fun j =>
    decodeTop aSize sites (Numbering.digit base packed (slot names j))

variable (a : Numbering A) (U : List (Prog.Loc A))

theorem decodePC_eq (q : Prog.Pc U) :
    decodePC (U.map (site (letter a))) ((pcs a U).equiv q).val = pcKey (letter a) U q := by
  cases q with
  | none =>
    change decodePC _ ((ptrNumbering (letter a) U).option.equiv none).val = none
    rw [Generator.StackRows.option_none]
    rfl
  | some p =>
    change decodePC _ ((ptrNumbering (letter a) U).option.equiv (some p)).val = some _
    rw [Generator.StackRows.option_some]
    simp only [decodePC, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    exact (ptr_read (letter a) U ((ptrNumbering (letter a) U).equiv p)).trans
      (by rw [Equiv.symm_apply_apply])

theorem decodeTop_eq (v : Option (Prog.Sym U)) :
    decodeTop a.size (U.map (site (letter a))) ((symbols a U).option.equiv v).val =
      v.map (symbolKey (letter a) U) := by
  cases v with
  | none => simp [decodeTop]
  | some v =>
    simp only [Generator.StackRows.option_some, decodeTop, Nat.add_one_ne_zero, ↓reduceIte,
      Nat.add_sub_cancel, Option.map_some]
    cases v with
    | inl x =>
      have h : ((symbols a U).equiv (.inl x)).val = (a.equiv x).val := rfl
      rw [h, ite_eq_left (a.equiv x).isLt]
      rfl
    | inr p =>
      have h : ((symbols a U).equiv (.inr p)).val = a.size + ((ptrNumbering (letter a) U).equiv p).val := rfl
      rw [h, ite_eq_right (by omega), Nat.add_sub_cancel_left]
      rw [ptr_read (letter a) U ((ptrNumbering (letter a) U).equiv p), Equiv.symm_apply_apply]
      rfl

omit [Fintype A] in
theorem slot_eq (j : Prog.Ix U) :
    slot (Prog.used U) (register U j) = ((Pack.stacks U).equiv j).val := by
  cases j with
  | none => exact (Generator.StackRows.option_none (idxNumbering U)).symm
  | some i =>
    change rank (Prog.used U) i.val + 1 = ((idxNumbering U).option.equiv (some i)).val
    rw [Generator.StackRows.option_some, idx_rank]

omit [Fintype A] in
private theorem register_lt (j : Prog.Ix U) :
    register U j < (Prog.used U).foldr max 0 + 2 := by
  cases j with
  | none => simp [register]
  | some i =>
    have hi : i.val ≤ (Prog.used U).foldr max 0 := List.le_max_of_le i.property le_rfl
    change i.val + 1 < _ + 2
    omega

/-- The unpacked finite list gives the correct read symbol at every actual stack,
including registers whose names are widely separated. -/
theorem heads_eq (top : Prog.Ix U → Option (Prog.Sym U)) (j : Prog.Ix U) :
    readHead (heads a.size (U.map (site (letter a)))
      (((Pack.stacks U).arrow (symbols a U).option).equiv top).val) (register U j) =
      (top j).map (symbolKey (letter a) U) := by
  simp only [readHead, heads, registerNames_sites, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (register_lt U j), Option.map_some, Option.getD_some, slot_eq]
  have digit := Numbering.digit_arrow (Pack.stacks U) (symbols a U).option top j
  exact (congrArg (decodeTop a.size (U.map (site (letter a)))) digit).trans (decodeTop_eq a U (top j))

end GeneratorSyntax.Pack

end NearSquareRoot
end Computability
end OAI
