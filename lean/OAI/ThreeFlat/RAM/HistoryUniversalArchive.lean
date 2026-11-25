import OAI.ThreeFlat.RAM.HistoryStaticArchive

namespace OAI
/-! # A single field-dependent fixed catalog for the complete base tensor library -/

namespace ThreeFlat.RAM.HistoryStaticArchive

open Diagonal
open scoped Classical
noncomputable section

variable (F : Type) [Fintype F] (B : ℕ)

abbrev Entry := (b : Fin (B+1)) × ((Fin b.val → Bool) → F)

def count := Fintype.card (Entry F B)

def all : Catalog F (count F B) B where
  arity i := ((Fintype.equivFin (Entry F B)).symm i).1.val
  fits i := Nat.le_of_lt_succ ((Fintype.equivFin (Entry F B)).symm i).1.isLt
  coeff i := ((Fintype.equivFin (Entry F B)).symm i).2

def index {b : ℕ} (room : b≤B) (f : (Fin b → Bool) → F) : Fin (count F B) :=
  Fintype.equivFin (Entry F B) ⟨⟨b,Nat.lt_succ_of_le room⟩,f⟩

private theorem entry_index {b : ℕ} (room : b≤B) (f : (Fin b → Bool) → F) :
    (Fintype.equivFin (Entry F B)).symm (index F B room f) = ⟨⟨b,Nat.lt_succ_of_le room⟩,f⟩ :=
  (Fintype.equivFin _).symm_apply_apply _

@[simp] theorem arity_index {b : ℕ} (room : b≤B) (f : (Fin b → Bool) → F) :
    (all F B).arity (index F B room f) = b := congrArg (fun e : Entry F B => e.1.val) (entry_index F B room f)

theorem coeff_index {b : ℕ} (room : b≤B) (f : (Fin b → Bool) → F) :
    HEq ((all F B).coeff (index F B room f)) f := by
  change HEq (((Fintype.equivFin (Entry F B)).symm (index F B room f)).2) _
  rw [entry_index]

theorem row_index [CommRing F] {b : ℕ} (room : b≤B) (f : (Fin b → Bool) → F) :
    HEq ((all F B).rows (index F B room f)) (ConstantKernelLUT.network f) := by
  change HEq (ConstantKernelLUT.network ((Fintype.equivFin (Entry F B)).symm (index F B room f)).2) _
  rw [entry_index]

end
end ThreeFlat.RAM.HistoryStaticArchive

end OAI
