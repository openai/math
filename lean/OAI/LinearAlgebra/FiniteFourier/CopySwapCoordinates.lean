import OAI.LinearAlgebra.FiniteFourier.SwapReweight
import OAI.LinearAlgebra.SpectralBooks.CopyLabelTensor

/-! # Coordinates of the two successive label copies on a weighted swap -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical

variable {G : Type} [Fintype G] {K : Type*} [Field K]

/-- Encode the fourth coordinate of the original swap. -/
def thirdSwapLabel (w : G × G → K) (b : ((swapRaw w).group some).Leg (some 3)) :
    Fin (Fintype.card G) := Fintype.equivFin G (b ⟨3,rfl⟩)

/-- Copy the fourth coordinate to the center. -/
def firstSwapCopy (w : G × G → K) : Raw (Option (Fin 4)) K :=
  ((swapRaw w).group some).appendLabel none (Fin (Fintype.card G))
    (fun x ↦ thirdSwapLabel w (x (some 3)))

/-- Encode the third coordinate of the original swap after the first copy. -/
def secondSwapLabel (w : G × G → K) (b : (firstSwapCopy w).Leg (some 2)) :
    Fin (Fintype.card G) := Fintype.equivFin G (b.1 ⟨2,rfl⟩)

/-- Copy the third coordinate to the same center. -/
def secondSwapCopy (w : G × G → K) : Raw (Option (Fin 4)) K :=
  (firstSwapCopy w).appendLabel none (Fin (Fintype.card G))
    (fun x ↦ secondSwapLabel w (x (some 2)))

private def swapCopyLegEquiv (w : G × G → K) (i : Option (Fin 4)) :
    (secondSwapCopy w).Leg i ≃ (copiedSwapRaw w).Leg i := by
  cases i with
  | none =>
    exact {
      toFun := fun b ↦ ((Fintype.equivFin G).symm (b.2 ⟨(),rfl⟩),
        (Fintype.equivFin G).symm (b.1.2 ⟨(),rfl⟩))
      invFun := fun p ↦ ((fun t ↦ (nomatch t.property), fun _ ↦ Fintype.equivFin G p.2),
        fun _ ↦ Fintype.equivFin G p.1)
      left_inv := by
        rintro ⟨⟨a,b⟩,c⟩
        apply Prod.ext
        · apply Prod.ext
          · funext t
            exact nomatch t.property
          · funext ⟨⟨⟩,_⟩
            exact (Fintype.equivFin G).apply_symm_apply _
        · funext ⟨⟨⟩,_⟩
          exact (Fintype.equivFin G).apply_symm_apply _
      right_inv := by
        rintro ⟨p,q⟩
        exact Prod.ext ((Fintype.equivFin G).symm_apply_apply p)
          ((Fintype.equivFin G).symm_apply_apply q) }
  | some i =>
    exact {
      toFun := fun b ↦ b.1.1 ⟨i,rfl⟩
      invFun := fun a ↦ ((fun t ↦ (Option.some.inj t.property).symm ▸ a,
        fun t ↦ (nomatch t.property)), fun t ↦ (nomatch t.property))
      left_inv := by
        rintro ⟨⟨a,b⟩,c⟩
        apply Prod.ext
        · apply Prod.ext
          · funext ⟨k,hk⟩
            cases Option.some.inj hk
            rfl
          · funext t
            exact nomatch t.property
        · funext t
          exact nomatch t.property
      right_inv := fun _ ↦ rfl }

/-- Reindexing the two appended central coordinates recovers the copied swap. -/
theorem secondSwapCopy_equivalent (w : G × G → K) :
    (secondSwapCopy w).Equivalent (copiedSwapRaw w) := by
  apply Raw.reindex_equivalent (swapCopyLegEquiv w)
  intro x
  let z (i : Fin 4) := (x (some i)).1.1 ⟨i,rfl⟩
  let e := Fintype.equivFin G
  let a := (x none).2 ⟨(),rfl⟩
  let b := (x none).1.2 ⟨(),rfl⟩
  have agree (u v : G) (c : K) :
      (@ite K (a = e u) (Classical.propDecidable _)
        (@ite K (b = e v) (Classical.propDecidable _) c 0) 0) =
      @ite K ((e.symm a, e.symm b) = (u,v)) (Classical.propDecidable _) c 0 := by
    simp only [Prod.mk.injEq, Equiv.symm_apply_eq]
    by_cases ha : a = e u <;> simp [ha]
  exact agree (z 2) (z 3) ((swapRaw w).coeff z)

end

end FiniteFourier
end LinearAlgebra
end OAI
