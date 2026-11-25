import OAI.LinearAlgebra.FiniteFourier.BatchedListTensor

/-! # Pairing two triangle lists at the center of the rectangle -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] {R C D : Type} [Fintype R] [Fintype C] [Fintype D]

private def leftSites : Fin 3 → Fin 5 := ![4,0,2]
private def rightSites : Fin 3 → Fin 5 := ![4,1,3]
private def corners : Fin 4 → Fin 5 := ![0,1,2,3]

private abbrev pairedLeg (R C : Type) (s : Fin 3 → Fin 5) (j : Fin 5) :=
  (i : {i // s i = j}) → listLeg R C i.val

private abbrev cornerLeg (C D : Type) (j : Fin 5) :=
  (i : {i // corners i = j}) → phaseLeg C D i.val

private def eqWeight {A : Type} (a b : A) : K := if a = b then 1 else 0

private def pairMap (K : Type*) [Field K] (R C D : Type) (j : Fin 5) :
    cornerLeg C D j → pairedLeg R C leftSites j × pairedLeg R D rightSites j → K := by
  revert j
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => i.elim0)))))
  · exact fun x t => eqWeight (A := C) (x ⟨0,rfl⟩) (t.1 ⟨1,rfl⟩)
  · exact fun x t => eqWeight (A := D) (x ⟨1,rfl⟩) (t.2 ⟨1,rfl⟩)
  · exact fun x t => eqWeight (A := C) (x ⟨2,rfl⟩) (t.1 ⟨2,rfl⟩)
  · exact fun x t => eqWeight (A := D) (x ⟨3,rfl⟩) (t.2 ⟨2,rfl⟩)
  · exact fun _ t => eqWeight (A := R) (t.1 ⟨0,rfl⟩) (t.2 ⟨0,rfl⟩)

private theorem paired_sum (U : Matrix R C K) (V : Matrix R D K) (a b : C) (c d : D) :
    (∑ r, (if a = b then U r a else 0) * (if c = d then V r c else 0)) =
    ∑ r, ∑ i, ∑ j, ∑ s, ∑ k, ∑ l, (if i = j then U r i else 0) *
      (if k = l then V s k else 0) * (eqWeight a i * eqWeight c k *
        eqWeight b j * eqWeight d l * eqWeight r s) := by
  simp [eqWeight, mul_ite, ite_mul, Finset.sum_ite_irrel]

theorem paired_list_restricts (U : Matrix R C K) (V : Matrix R D K) :
    ((phaseRaw (Uᵀ * V)).group corners).Restricts
      (((listRaw U).group leftSites).mul ((listRaw V).group rightSites)) := by
  let coord (A : Type) : (R × A × A) ≃ (∀ i, listLeg R A i) :=
    { toFun := fun p => listCoordinates p.1 p.2.1 p.2.2
      invFun := fun z => (z 0, z 1, z 2)
      left_inv := fun _ => rfl
      right_inv := fun z => by funext i; fin_cases i <;> rfl }
  let T := ((listRaw U).group leftSites).mul ((listRaw V).group rightSites)
  let e : ((R × C × C) × (R × D × D)) ≃ (∀ j, T.Leg j) :=
    ((coord C).prodCongr (coord D)).trans
      (((groupIndexEquiv leftSites (listRaw U).Leg).prodCongr
        (groupIndexEquiv rightSites (listRaw V).Leg)).trans
        (Equiv.arrowProdEquivProdArrow (Fin 5) ((listRaw U).group leftSites).Leg
          ((listRaw V).group rightSites).Leg).symm)
  refine ⟨pairMap K R C D, fun x => ?_⟩
  let f (q : ∀ j, T.Leg j) := T.coeff q * ∏ j, pairMap K R C D j (x j) (q j)
  let : DecidableEq (Fin 5) := Classical.decEq _
  refine Eq.trans ?_ (e.sum_comp f)
  simp only [Fintype.sum_prod_type]
  let z : ∀ i, phaseLeg C D i := fun i => x (corners i) ⟨i,rfl⟩
  refine (listRaw_pair U V z).trans ?_
  simp only [f, Fin.prod_univ_five]
  exact paired_sum U V (z 0) (z 2) (z 1) (z 3)

theorem paired_list_price_le (P : SpectralPlacementPrices K Plane)
    (U : Matrix R C K) (V : Matrix R D K)
    (hu : (listRaw U).coeff ≠ 0) (hv : (listRaw V).coeff ≠ 0)
    (a b c d x : Plane) :
    fourierPhasePrice P (Uᵀ * V) ![a,c,b,d] ≤
      P.price (listRaw U) ![x,a,b] + P.price (listRaw V) ![x,c,d] := by
  let sites : Fin 5 → Plane := ![a,c,b,d,x]
  have h := placed_price_mono P sites (paired_list_restricts U V)
  have hc : sites ∘ corners = ![a,c,b,d] := by funext i; fin_cases i <;> rfl
  have hl : sites ∘ leftSites = ![x,a,b] := by funext i; fin_cases i <;> rfl
  have hr : sites ∘ rightSites = ![x,c,d] := by funext i; fin_cases i <;> rfl
  rw [placed_price_mul P sites _ _ (((listRaw U).group_ne_zero_iff _).mpr hu)
    (((listRaw V).group_ne_zero_iff _).mpr hv), ← P.group, ← P.group, ← P.group,
    hc, hl, hr] at h
  exact h

end
end FiniteFourier
end LinearAlgebra
end OAI
