import OAI.Computability.NearSquareRoot.SynchronizedPlacedWord
import OAI.Computability.NearSquareRoot.SynchronizedBlockSlots

/-! # Placed butterflies on a completed physical matching

A complete routing table agrees with the placed butterflies on every active
pair. On the remaining pairs the placed operator fixes both cells.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix SynchronizedPair
open scoped Matrix

variable {X C J A S : Type} [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A] [Fintype S] [DecidableEq S]

omit [DecidableEq A] in
private theorem paired_mulVec (f : A ≃ Fin 2 × S) (M : S → PairMatrix)
    (x : A → ℂ) (b : Fin 2) (s : S) :
    ((blockDiagonal M).submatrix f f *ᵥ x) (f.symm (b,s)) =
      (M s *ᵥ (fun bit => x (f.symm (bit,s)))) b := by
  rw [submatrix_mulVec_equiv]
  simp [mulVec, dotProduct, Fintype.sum_prod_type, blockDiagonal_apply, ite_mul, Finset.sum_ite_eq]

/-- A placement of a fixed-bit Walsh is exactly the completed matching of
Walsh gates on its labelled pairs and identity gates on all other pairs.
The match and its action are supplied by the physical routing table. -/
theorem placeWalsh_matching (f : X ≃ Fin 2 × C) (e : X × J ↪ A) (matching : Fin 2 × S ≃ A)
    (label : C × J → S) (active : S → Bool) (hs : ∀ s, active s = true ↔ s ∈ Set.range label)
    (hmatch : ∀ bit c j, matching (bit,label (c,j)) = e (f.symm (bit,c),j)) :
    placeHom e (Slot.matrix f .walsh) =
      (blockDiagonal (fun s => if active s then walsh else 1)).submatrix matching.symm matching.symm := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  funext y
  obtain ⟨⟨b,s⟩, rfl⟩ := matching.surjective y
  have hout := paired_mulVec matching.symm (fun s => if active s then walsh else 1) x b s
  simp only [Equiv.symm_symm] at hout
  rw [hout]
  by_cases on : active s = true
  · obtain ⟨⟨c,j⟩, rfl⟩ := (hs s).1 on
    rw [ite_eq_left on, hmatch, placeHom_mulVec, e.injective.extend_apply]
    change (((blockDiagonal (fun _ : C => walsh)).submatrix f f) *ᵥ _) (f.symm (b,c)) = _
    rw [paired_mulVec]
    simp only [hmatch]
  · have idle : matching (b,s) ∉ Set.range e := by
      rintro ⟨⟨u,j⟩, he⟩
      obtain ⟨⟨bit,c⟩, rfl⟩ := f.symm.surjective u
      have hpair := matching.injective ((hmatch bit c j).trans he)
      exact on ((hs s).2 ⟨(c,j), congrArg Prod.snd hpair⟩)
    rw [ite_eq_right on, Matrix.one_mulVec, placeHom_mulVec, Function.extend_apply' _ _ _ idle]

end ShortFourier

end NearSquareRoot
end Computability
end OAI
