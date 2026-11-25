import OAI.Computability.BorderVNP.PackedBottomGridSite
import OAI.Computability.BorderVNP.CellSparseSignedResult

/-! # The complete local observation of a repeated bottom box

The original immutable factor list may consist of Boolean guards, selected
field positions or signed checks. All use the same one-copy wiring and repeat
layout. The cell reader tests every actual copy and each public incidence row.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomRepeat

open Crossing CellSparse Inherited BottomReports
open scoped Classical

variable {D qe qa : ℕ} {A : Type} [Fintype A] {width : A → ℕ}
variable (N : Network D A width) (edges : N.Edge ↪ Fin qe) (ports : A ↪ Fin qa) (v : N.Site)

/-- An original site with one arbitrary, already staged immutable private box and
one public tie per grouped incidence word. The native box record always has ID zero. -/
noncomputable def bornWith (copies capFine stride : ℕ) (box : List Factor) : Site :=
  ⟨copies*stride,incoming (wide N copies) v,[box],
    [[.box 0 0 copies stride] ++ ties N edges ports v copies capFine stride]⟩

/-- The ordered factor occurrences in the actual private evaluator. -/
theorem bornWith_occurrences (copies capFine stride : ℕ) (box : List Factor) :
    (bornWith N edges ports v copies capFine stride box).directory.occurrences =
      (List.range copies).flatMap (fun i => box.map (fun f => (⟨f,i*stride,i⟩ : Occurrence))) := by
  simp only [Directory.occurrences,Site.directory,bornWith,Site.rows,List.reverse_singleton,List.flatten_cons,
    List.flatten_nil,List.append_nil,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.getD_eq_getElem?_getD,List.getElem?_cons_zero,Option.getD_some,Nat.zero_add]
  have discard {T : Type} (xs ys : List T) (h : ys = []) : xs++ys = xs := by simp [h]
  apply discard
  apply List.flatMap_eq_nil_iff.mpr
  intro r hr
  obtain ⟨z,_,rfl⟩ := List.mem_map.mp hr
  rfl

/-- This site's public pass condition consists precisely of its incidence ties. -/
theorem bornWith_rows_valid (copies capFine stride : ℕ) (box : List Factor) (bank : ℕ → Bool) :
    let s := bornWith N edges ports v copies capFine stride box
    (∀ r ∈ s.rows, r.Valid s.boxes bank) ↔ ∀ r ∈ ties N edges ports v copies capFine stride,
      r.Valid [box] bank := by
  simp only [bornWith,Site.rows,List.reverse_singleton,List.flatten_cons,List.flatten_nil,List.append_nil,
    List.singleton_append,List.forall_mem_cons,Record.Valid,List.length_cons,List.length_nil]
  simp

open private mapM_present from OAI.Computability.BorderVNP.PackedGridDirectory

/-- The private program succeeds exactly when its physical public records and all
original factors at their actual copy offsets succeed. -/
theorem bornWith_accepts (copies capFine stride : ℕ) (box : List Factor) (bank : ℕ → Bool) :
    ((bornWith N edges ports v copies capFine stride box).observe bank).isSome = true ↔
      (∀ r ∈ ties N edges ports v copies capFine stride, r.Valid [box] bank) ∧
      ∀ i < copies, ∀ f ∈ box, (f.observe bank (i*stride) i).isSome = true := by
  let site := bornWith N edges ports v copies capFine stride box
  have pass := bornWith_rows_valid N edges ports v copies capFine stride box bank
  by_cases h : ∀ r ∈ site.rows, r.Valid site.boxes bank
  · rw [Site.observe,ite_eq_left h,Directory.observations,mapM_present,bornWith_occurrences,
      and_iff_right (pass.mp h)]
    simp only [List.mem_flatMap,List.mem_range,List.mem_map,forall_exists_index,and_imp]
    constructor
    · intro hh i hi f hf
      exact hh _ i hi f hf rfl
    · rintro hh _ i hi f hf rfl
      exact hh i hi f hf
  · rw [Site.observe,ite_eq_right h]
    simp only [Option.isSome_none,Bool.false_eq_true,false_iff,not_and]
    intro ht
    exact (h (pass.mpr ht)).elim

/-- A factor's whole data dependence is on relative lanes below the copy stride. -/
def FactorWithin (n : ℕ) : Factor → Prop
  | .truth ws _ | .sign ws _ | .gadget ws _ => ∀ k ∈ ws, k < n
  | .unary _ _ => False

private theorem word_agrees (x y : ℕ → Bool) (off : ℕ) (ws : List ℕ)
    (h : ∀ k ∈ ws, x (off+k) = y (off+k)) :
    word x (ws.map (off+·)) = word y (ws.map (off+·)) := by
  induction ws with
  | nil => rfl
  | cons k ks ih =>
    obtain ⟨hk,hks⟩ := List.forall_mem_cons.mp h
    simp [word,hk,ih hks]

/-- Two banks agreeing on the copy produce exactly the same observation, including
gadget identity and sign. -/
theorem factor_agrees (n : ℕ) (f : Factor) (hf : FactorWithin n f) (x y : ℕ → Bool) (off copy : ℕ)
    (h : ∀ k < n, x (off+k) = y (off+k)) : f.observe x off copy = f.observe y off copy := by
  cases f with
  | truth ws _ | sign ws _ | gadget ws _ =>
    simp only [Factor.observe,word_agrees x y off ws (fun k hk => h k (hf k hk))]
  | unary => exact hf.elim

end Packing.BottomRepeat

end BorderVNP
end Computability
end OAI
