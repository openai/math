import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace OAI
/-! # Physical row numbers of original route occurrences and their adjacent turns -/

noncomputable section
namespace Hierarchy.ProtocolRAMTurnOrder

open scoped BigOperators Classical

variable {k : ℕ}

def width (length : Fin k → ℕ) (i : Fin k) := length i+1

def turns (length : Fin k → ℕ) := ∑ i,width length i

def origin (length : Fin k → ℕ) (i : Fin k) := ∑ j : Fin i.val,length (j.castLE i.isLt.le)

def encode (len : Fin k → ℕ) : ((i : Fin k) × Fin (len i)) ≃ Fin (∑ j,len j) :=
  finSigmaFinEquiv

theorem encode_val (len : Fin k → ℕ) (i : Fin k) (j : Fin (len i)) :
    (encode len ⟨i,j⟩).val=origin len i+j.val := finSigmaFinEquiv_apply _

def raw (len : Fin k → ℕ) (i : Fin (turns len)) : (a : Fin k) × Fin (len a+1) :=
  (encode (width len)).symm i

theorem raw_encode (len : Fin k → ℕ) (i : Fin k) (j : Fin (len i+1)) :
    raw len (encode (width len) ⟨i,j⟩)=⟨i,j⟩ :=
  (encode (width len)).symm_apply_apply _

theorem row_eq (len : Fin k → ℕ) (i : Fin (turns len)) :
    i.val=origin (width len) (raw len i).1+(raw len i).2.val := by
  calc
    i.val=((encode (width len)) (raw len i)).val :=
      (congrArg Fin.val ((encode (width len)).apply_symm_apply i)).symm
    _ = _ := encode_val (width len) (raw len i).1 (raw len i).2

theorem has_previous (len : Fin k → ℕ) (i : Fin (turns len)) (h : 0 < (raw len i).2.val) :
    0 < i.val := by rw [row_eq len i];omega

/-- The immediately preceding native row is genuinely the previous boundary of
the same commodity, even when the preceding commodity had an empty route. -/
theorem previous_eq (len : Fin k → ℕ) (i : Fin (turns len)) (h : 0 < (raw len i).2.val) :
    raw len ⟨i.val-1,(Nat.sub_le ..).trans_lt i.isLt⟩ =
      ⟨(raw len i).1,⟨(raw len i).2.val-1,(Nat.sub_le ..).trans_lt (raw len i).2.isLt⟩⟩ := by
  apply (encode (width len)).injective
  rw [show (encode (width len)) (raw len ⟨i.val-1,(Nat.sub_le ..).trans_lt i.isLt⟩)=
      ⟨i.val-1,(Nat.sub_le ..).trans_lt i.isLt⟩ from (encode (width len)).apply_symm_apply _]
  apply Fin.ext
  have loc := row_eq len i
  have arithmetic : i.val-1=origin (width len) (raw len i).1+((raw len i).2.val-1) := by omega
  exact arithmetic.trans (encode_val (width len) (raw len i).1
    ⟨(raw len i).2.val-1,(Nat.sub_le ..).trans_lt (raw len i).2.isLt⟩).symm

def boundary (length : ℕ) (reverse : Bool) : Fin (length+1) ≃ Fin (length+1) :=
  if reverse then Fin.revPerm else Equiv.refl _

theorem boundary_val (length : ℕ) (reverse : Bool) (j : Fin (length+1)) :
    (boundary length reverse j).val=if reverse then length-j.val else j.val := by
  cases reverse <;> simp [boundary,Fin.revPerm,Fin.rev]

/-- Canonical chord order may reverse a walk. It only permutes the boundaries
of that single source, preserving the distinctness of all original turn rows. -/
def visits (len : Fin k → ℕ) (reverse : Fin k → Bool) :
    Fin (turns len) ≃ ((a : Fin k) × Fin (len a+1)) :=
  (encode (width len)).symm.trans (Equiv.sigmaCongrRight fun a=>boundary (len a) (reverse a))

theorem visits_val (len : Fin k → ℕ) (reverse : Fin k → Bool) (i : Fin (turns len)) :
    (visits len reverse i).2.val =
      if reverse (raw len i).1 then len (raw len i).1-(raw len i).2.val else (raw len i).2.val :=
  boundary_val ..

theorem turns_eq (len : Fin k → ℕ) : turns len=(∑ i,len i)+k := by
  simp [turns,width,Finset.sum_add_distrib]

end Hierarchy.ProtocolRAMTurnOrder

end
end OAI
