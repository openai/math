import OAI.LinearAlgebra.SpectralBooks.TensorGroupRaw

/-! # Local maps controlled by an existing basis index

At each occupied site, retain the old basis index and act on every auxiliary
leg in its fiber using a matrix selected by that index.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped BigOperators Classical

namespace SiteTensor.Raw

variable {H J : Type} {K : Type*} [Fintype H] [Fintype J] [CommSemiring K]

/-- Apply the auxiliary matrices, retaining the controlling coordinate. -/
def controlledContraction (f : H → J) (T : Raw.{0} J K) (U : Raw.{0} H K)
    (D : H → Type) [∀ h, Fintype (D h)]
    (M : ∀ h, T.Leg (f h) → D h → U.Leg h → K) : Raw.{0} J K where
  Leg j := T.Leg j × ((h : {h // f h = j}) → D h.1)
  finiteLeg _ := inferInstance
  coeff y := T.coeff (fun j => (y j).1) *
    ∑ z, U.coeff z * ∏ h, M h (y (f h)).1 ((y (f h)).2 ⟨h, rfl⟩) (z h)

/-- The controlled contraction is a restriction of the old tensor times the
grouped auxiliary tensor, including when the placement has collisions. -/
theorem restrict_controlled_contraction (f : H → J) (T : Raw.{0} J K) (U : Raw.{0} H K)
    (D : H → Type) [∀ h, Fintype (D h)]
    (M : ∀ h, T.Leg (f h) → D h → U.Leg h → K) :
    (controlledContraction f T U D M).Restricts (T.mul (U.group f)) := by
  classical
  let localMap (j : J) (b : T.Leg j) (d : (h : {h // f h = j}) → D h.1)
      (u : (h : {h // f h = j}) → U.Leg h.1) :=
    ∏ h, M h.1 (h.2.symm ▸ b) (d h) (u h)
  refine ⟨fun j y x => (if x.1 = y.1 then 1 else 0) * localMap j y.1 y.2 x.2, fun y => ?_⟩
  let old : ∀ j, T.Leg j := fun j => (y j).1
  let factor (z : ∀ h, U.Leg h) := ∏ h, M h (old (f h)) ((y (f h)).2 ⟨h, rfl⟩) (z h)
  let e := (Equiv.arrowProdEquivProdArrow J T.Leg (U.group f).Leg).trans
    (Equiv.prodCongr (Equiv.refl _) (groupIndexEquiv f U.Leg).symm)
  have hf (z : ∀ h, U.Leg h) :
      (∏ j, localMap j (old j) (y j).2 (groupIndexEquiv f U.Leg z j)) = factor z := by
    let w (p : Σ j, {h // f h = j}) :=
      M p.2.1 (p.2.2.symm ▸ old p.1) ((y p.1).2 p.2) (z p.2.1)
    calc
      _ = ∏ p, w p := (Fintype.prod_sigma w).symm
      _ = _ := (Fintype.prod_equiv (Equiv.sigmaFiberEquiv f).symm _ _ (fun _ => rfl)).symm
  change T.coeff old * ∑ z, U.coeff z * factor z = _
  symm
  calc
    _ = ∑ p : (∀ j, T.Leg j) × (∀ h, U.Leg h),
        T.coeff p.1 * U.coeff p.2 *
          (∏ j, (if p.1 j = old j then 1 else 0) *
            localMap j (old j) (y j).2 (groupIndexEquiv f U.Leg p.2 j)) := by
      apply Fintype.sum_equiv e
      intro x
      have hz : groupIndexEquiv f U.Leg (e x).2 = fun j => (x j).2 :=
        (groupIndexEquiv f U.Leg).apply_symm_apply _
      rw [hz]
      rfl
    _ = _ := by
      simp_rw [Finset.prod_mul_distrib, Fintype.prod_boole, ← funext_iff, hf]
      rw [Fintype.sum_prod_type]
      simp_rw [ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
      simp [Finset.mul_sum, mul_assoc]

/-- Retain the old labels and apply local matrices to a common auxiliary label. -/
def controlledDiagonal (f : H → J) (T : Raw.{0} J K)
    (D : H → Type) [∀ h, Fintype (D h)] (L : ℕ)
    (M : ∀ h, T.Leg (f h) → D h → Fin L → K) : Raw.{0} J K where
  Leg j := T.Leg j × ((h : {h // f h = j}) → D h.1)
  finiteLeg _ := inferInstance
  coeff y := T.coeff (fun j => (y j).1) *
    ∑ l, ∏ h, M h (y (f h)).1 ((y (f h)).2 ⟨h, rfl⟩) l

/-- A single grouped diagonal supplies the common summation label. -/
theorem restrict_controlled_diagonal (f : H → J) (T : Raw.{0} J K)
    (D : H → Type) [∀ h, Fintype (D h)] (L : ℕ)
    (M : ∀ h, T.Leg (f h) → D h → Fin L → K) :
    (controlledDiagonal f T D L M).Restricts (T.mul ((diagonal H K (Fin L)).group f)) := by
  have he : (controlledDiagonal f T D L M).coeff =
      (controlledContraction f T (diagonal H K (Fin L)) D M).coeff := by
    funext y
    simp only [controlledDiagonal, controlledContraction, diagonal]
    congr 1
    simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm]
    simp
  unfold Restricts
  rw [he]
  exact restrict_controlled_contraction f T (diagonal H K (Fin L)) D M

end SiteTensor.Raw

end

end SpectralBooks
end LinearAlgebra
end OAI
