import OAI.Computability.BorderVNP.PackedBottomScalarValue

/-! # Reindexing original boxes whose report bits depend on their fine wires

A report in an unlinked original site is forced by its selected fine bit.
Thus the complete work-bank bijection must allow the vector of prescribed
report bits to depend on the tuple of free fine guesses.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open Inherited BottomRepeat
open scoped Classical
open private bits_left from OAI.Computability.BorderVNP.PackedInheritedStaging
open private work_bit from OAI.Computability.BorderVNP.PackedBottomScalarValue

/-- Extract all independent fine guesses from their actual copies of a flat work bank. -/
def Slab.decodeWork (s : Slab) (b : ℕ) (work : Fin (b*s.stride) → Bool) (i : Fin b) : Fin s.guessed → Bool :=
  s.extractGuess (fun j => work (finProdFinEquiv (i,j)))

variable (s : Slab) (b : ℕ) (u : Fin b → Fin s.supplied → Bool) (x : Fin b → Fin s.incoming → Bool)
variable (uses : (Fin b → Fin s.guessed → Bool) → Fin b → Fin s.used → Bool)

/-- The physical checks with each report taken from the tuple of original wire
guesses decoded at the front of the corresponding private work slabs. -/
def Slab.DynamicChecks (work : Fin (b*s.stride) → Bool) : Prop :=
  WorkChecks s b u x (uses (s.decodeWork b work)) work

/-- Reading the guessed prefixes of a canonical completion recovers exactly its
original fine choices regardless of the prescribed reports. -/
theorem Slab.decode_checked (r : Fin b → Fin s.used → Bool) (g : Fin b → Fin s.guessed → Bool) :
    s.decodeWork b ((s.checkedGuessEquiv b u x r g).val) = g :=
  (s.checkedGuessEquiv b u x r).symm_apply_apply g

/-- Original fine choices biject with the physical work assignments satisfying
all the dependent copy reports, even when some selected bits are false. -/
noncomputable def Slab.dynamicGuessEquiv :
    (Fin b → Fin s.guessed → Bool) ≃ {work : Fin (b*s.stride) → Bool // s.DynamicChecks b u x uses work} where
  toFun g := ⟨(s.checkedGuessEquiv b u x (uses g) g).val,by
    rw [Slab.DynamicChecks,s.decode_checked]
    exact (s.checkedGuessEquiv b u x (uses g) g).property⟩
  invFun w := s.decodeWork b w.val
  left_inv g := s.decode_checked b u x (uses g) g
  right_inv w := by
    apply Subtype.ext
    let r := uses (s.decodeWork b w.val)
    let w' : {work // WorkChecks s b u x r work} := ⟨w.val,w.property⟩
    have eq := congrArg (fun w : {work // WorkChecks s b u x r work} => w.val)
      ((s.checkedGuessEquiv b u x r).apply_symm_apply w')
    exact eq

/-- On the exact fine-wire prefix, the private bank reads its decoded guess or
the corresponding supplied value. This needs only the supplied-lane part of
the copy checks and holds before determining any report bit. -/
theorem Slab.readFine {d : ℕ} (work : Fin (b*s.stride) → Bool) (input : Fin d → Bool) (i : Fin b)
    (supplied : Fin s.supplied → Bool)
    (hs : ∀ j : Fin s.supplied, bits work input (i.val*s.stride+(s.guessed+j.val)) = supplied j)
    (k : Fin (s.guessed+s.supplied)) :
    bits work input (i.val*s.stride+k.val) =
      (finSumFinEquiv.symm k).elim (s.decodeWork b work i) supplied := by
  obtain ⟨z,rfl⟩ := finSumFinEquiv.surjective k
  rcases z with a | j
  · simp only [finSumFinEquiv_symm_apply_castAdd,Sum.elim_inl,finSumFinEquiv_apply_left,Fin.val_castAdd]
    have hk : a.val < s.stride := by
      have hf := s.fineFits
      have ha := a.isLt
      change a.val < s.capFine+s.incoming+s.capReport
      omega
    exact work_bit work input i ⟨a.val,hk⟩
  · simp only [finSumFinEquiv_symm_apply_natAdd,Sum.elim_inr,finSumFinEquiv_apply_right,Fin.val_natAdd]
    exact hs j

/-- The bounded work-bank criteria in the bijection coincide with the original
natural addresses of the private interpreter. -/
theorem Slab.workChecks_bits {d : ℕ} (work : Fin (b*s.stride) → Bool) (input : Fin d → Bool)
    (r : Fin b → Fin s.used → Bool) :
    WorkChecks s b u x r work ↔
      ∀ i : Fin b, s.Checks (fun j => bits work input (i.val*s.stride+j)) (u i) (x i) (r i) := by
  apply forall_congr'
  intro i
  rw [s.checks_iff,s.checks_iff]
  have he : (fun k : Fin s.stride => bits work input (i.val*s.stride+k.val)) =
      fun k : Fin s.stride => if hk : k.val < s.stride then work (finProdFinEquiv (i,⟨k.val,hk⟩)) else false := by
    funext k
    simp only [k.isLt,dite_true,Fin.eta]
    exact work_bit work input i k
  rw [he]

end Packing.BottomReports

end BorderVNP
end Computability
end OAI
