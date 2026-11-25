import OAI.Computability.BorderVNP.PackedInheritedHookBlock
import Mathlib.Data.Prod.Lex

/-! # Stable order and complete filtering of the frozen hook rectangles -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.HookTape

open InheritedHook
open scoped Classical

variable {old D : ℕ}

/-- Old cable row first, then direction, then source/destination flag. -/
private def orderKey (r : Row old D) : Fin old ×ₗ (Fin D ×ₗ Bool) := toLex (r.1,toLex r.2)

private abbrev Key (old D : ℕ) := Fin old ×ₗ (Fin D ×ₗ Bool)
private def unpack (r : Key old D) : Row old D := (ofLex r |>.1,ofLex (ofLex r).2)

/-- One reserved row per old cable, direction, and orientation in public old-row order. -/
noncomputable def rows (old D : ℕ) : List (Row old D) :=
  (Finset.univ : Finset (Key old D)).sort.map unpack

theorem mem_rows (r : Row old D) : r ∈ rows old D :=
  List.mem_map.mpr ⟨orderKey r,by simp,rfl⟩

/-- The fixed rectangle has exactly two orientations for every old row and direction. -/
theorem rows_length : (rows old D).length = old*(D*2) := by
  simp [rows,Key,Fintype.card_prod]

private theorem sorted_rows : (rows old D).Pairwise (fun u v => orderKey u < orderKey v) := by
  rw [rows,List.pairwise_map]
  exact (Finset.univ : Finset (Key old D)).sortedLT_sort.pairwise

/-- A terminal mask selects exactly its eligible sorted cable list from the
static rectangle. Width zero and unused old cable slots require no exceptions. -/
theorem filtered {Z : Type*} (cables : List Z) (slot : Z ↪ Fin old) (d : Fin D) (src : Z → Bool)
    (p : Row old D → Bool) (hp : ∀ r, p r = true ↔ ∃ z ∈ cables, r = (slot z,d,src z))
    (hs : cables.Pairwise (fun u v => slot u < slot v)) :
    (rows old D).filter p = cables.map fun z => (slot z,d,src z) := by
  let f (z : Z) : Row old D := (slot z,d,src z)
  have hright : (cables.map f).Pairwise (fun u v => orderKey u < orderKey v) := by
    rw [List.pairwise_map]
    exact hs.imp (fun huv => Prod.Lex.toLex_lt_toLex.mpr (Or.inl huv))
  have hleft := (sorted_rows (old := old) (D := D)).sublist (List.filter_sublist (p := p))
  have hperm : ((rows old D).filter p).Perm (cables.map f) := by
    have hl := hleft.imp (fun h e => (ne_of_lt h) (congrArg orderKey e))
    have hr := hright.imp (fun h e => (ne_of_lt h) (congrArg orderKey e))
    apply (List.perm_ext_iff_of_nodup hl hr).mpr
    intro r
    simp only [List.mem_filter,mem_rows,true_and,hp,List.mem_map]
    exact ⟨fun ⟨z,hz,he⟩ => ⟨z,hz,he.symm⟩,fun ⟨z,hz,he⟩ => ⟨z,hz,he.symm⟩⟩
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ huv hvu => False.elim (lt_asymm huv hvu)) hleft hright hperm

end Packing.Inherited.HookTape

end BorderVNP
end Computability
end OAI
