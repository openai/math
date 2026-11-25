import OAI.Computability.BorderVNP.CellDirectoryMerge
import OAI.Computability.BorderVNP.CellDirectoryBoxRebase
import OAI.Computability.BorderVNP.PackedBankBoxOrdinal

/-! # Retaining a site's private records through box-table relocation

New hook records follow the retained records at an old site. Rebasing an old box
ordinal preserves the lookup of its one-copy factors in the new cell. The proof
keeps the sparse syntax and the expanded multiplicities as separate counts.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Directory

theorem recordNodes_append (a b : List Record) :
    recordNodes (a++b) = recordNodes a+recordNodes b := by simp [recordNodes]; omega

theorem tableNodes_append (a b : List (List Factor)) :
    tableNodes (a++b) = tableNodes a+tableNodes b := by simp [tableNodes]; omega

theorem blockNodes_append (a b : List BoxBlock) :
    blockNodes (a++b) = blockNodes a+blockNodes b := by simp [blockNodes]

theorem resolvedRows_append (table : List (List Factor)) (a b : List Record) :
    resolvedRows table (a++b) = resolvedRows table a++resolvedRows table b := List.filterMap_append

private theorem recordNodes_rebase (rs : List Record) (base : ℕ) :
    recordNodes (rs.map (Record.rebaseBox base)) = recordNodes rs := by
  simp only [recordNodes,List.length_map,List.map_map,Function.comp_def,Record.rebaseBox_guardMassBound]

/-- Complete accounting of the old site's retained rows followed by its new public rows.
The first factor-lookup hypothesis is a valid local box reference. The second is the
actual ordinal guarantee of the stable owner sort. -/
theorem retained_charges (old : Directory) (table : List (List Factor)) (offset : ℕ)
    (extra : List Record) (h : ∀ r ∈ old.records, r.BoxRefFits old.boxes.length)
    (get : ∀ i < old.boxes.length, table.getD (offset+i) [] = old.boxes.getD i []) :
    let rs := old.records.map (Record.rebaseBox offset) ++ extra
    let fresh := resolvedRows table extra
    recordNodes rs = recordNodes old.records + recordNodes extra ∧
      blockNodes (resolvedRows table rs) = blockNodes old.blocks + blockNodes fresh ∧
      ((resolvedRows table rs).map fun b => b.copies*b.factors.length).sum =
        old.visitCount + (fresh.map fun b => b.copies*b.factors.length).sum := by
  dsimp only
  have eqn : resolvedRows table (old.records.map (Record.rebaseBox offset)) = old.blocks :=
    old.blocks_rebaseBoxes_of_getD table offset h get
  rw [recordNodes_append,recordNodes_rebase,resolvedRows_append,eqn,blockNodes_append,List.map_append,List.sum_append]
  exact ⟨rfl,rfl,rfl⟩

/-- A stable sort by physical owner supplies the exact prefix base and factor lookup
needed by each retained old site. -/
theorem retained_sorted {s : ℕ} (owner : Fin s → ℕ) (old : Fin s → Directory)
    (v : Fin s) (extra : List Record) (valid : ∀ r ∈ (old v).records, r.BoxRefFits (old v).boxes.length) :
    let boxes := fun i => (old i).boxes
    let table := Packing.BankBoxOrdinal.table owner boxes (owner v)
    let offset := Packing.BankBoxOrdinal.base owner (fun i => (boxes i).length) v
    let rs := (old v).records.map (Record.rebaseBox offset) ++ extra
    let fresh := resolvedRows table extra
    recordNodes rs = recordNodes (old v).records + recordNodes extra ∧
      blockNodes (resolvedRows table rs) = blockNodes (old v).blocks + blockNodes fresh ∧
      ((resolvedRows table rs).map fun b => b.copies*b.factors.length).sum =
        (old v).visitCount + (fresh.map fun b => b.copies*b.factors.length).sum := by
  intro boxes table offset
  apply retained_charges _ _ _ _ valid
  intro i hi
  have h := Packing.BankBoxOrdinal.table_get owner boxes v ⟨i,hi⟩
  rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem _ _ hi]
  rw [show table[offset+i]? = some ((old v).boxes[i]) from h]
  rfl

/-- A pure wire hook adds no factor visits, regardless of its copy and lane counts.
Its descriptor still contributes to public syntax in every occupied site. -/
theorem resolvedRows_wires (table : List (List Factor)) (rows : List Record)
    (hw : ∀ r ∈ rows, ∀ id base copies stride, r ≠ .box id base copies stride) :
    resolvedRows table rows = [] := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    have hh := ih fun s hs => hw _ (.tail _ hs)
    cases r with
    | box id base c stride => exact (hw _ List.mem_cons_self _ _ _ _ rfl).elim
    | zero | equal | profile => exact hh

end CellSparse.Directory

end BorderVNP
end Computability
end OAI
