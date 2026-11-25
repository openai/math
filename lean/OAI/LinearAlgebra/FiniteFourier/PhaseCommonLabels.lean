import OAI.LinearAlgebra.FiniteFourier.TriangleLabelPrice
import OAI.LinearAlgebra.SpectralBooks.PlacementDiagonal
import OAI.LinearAlgebra.SpectralBooks.DiagonalProduct

/-! # Construction of a phase from two shared triangle labels

The fifth site receives both labels and evaluates the coefficient `M x y`.
The four terminal maps keep the two prescribed copies of each label. Grouping
permits the center to coincide with any terminal.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical

private def rowTriangle : Fin 3 ↪ Fin 5 := ⟨![0, 2, 4], by decide⟩
private def colTriangle : Fin 3 ↪ Fin 5 := ⟨![1, 3, 4], by decide⟩
private def rows : Finset (Fin 5) := {0, 2, 4}
private def cols : Finset (Fin 5) := {1, 3, 4}
private abbrev PairLeg (O I : Type) (j : Fin 5) := MaskLeg rows O j × MaskLeg cols I j
private instance pairLegFintype {O I : Type} [Fintype O] [Fintype I] (j : Fin 5) :
    Fintype (PairLeg O I j) := Fintype.ofFinite _
private def pairTerm {O I : Type} (p : O × I) (j : Fin 5) : PairLeg O I j :=
  (fun _ ↦ p.1, fun _ ↦ p.2)
private def five {B : Fin 5 → Sort*} (v₀ : B 0) (v₁ : B 1) (v₂ : B 2) (v₃ : B 3) (v₄ : B 4) : ∀ i, B i :=
  Fin.cases v₀ (Fin.cases v₁ (Fin.cases v₂ (Fin.cases v₃ (Fin.cases v₄ (fun i ↦ i.elim0)))))

variable {K : Type*} {O I : Type} [Field K] [Fintype O] [Fintype I]

/-- The four-site phase padded by a trivial center is a restriction of the two
three-site common diagonals in their indicated local formats. -/
theorem phase_restricts_triangle_labels (M : Matrix O I K) :
    ((phaseRaw M).group Fin.castSucc).Restricts
      (((Raw.diagonal (Fin 3) K O).group rowTriangle).mul
        ((Raw.diagonal (Fin 3) K I).group colTriangle)) := by
  let T : Raw (Fin 5) K := ⟨PairLeg O I, inferInstance, Crossing.basisTensor pairTerm⟩
  have hprod : ofRaw T = ofRaw ((Raw.diagonal (Fin 3) K O).group rowTriangle) *
      ofRaw ((Raw.diagonal (Fin 3) K I).group colTriangle) := by
    rw [Raw.ofRaw_group_diagonal_eq_mask rowTriangle rows (by decide),
      Raw.ofRaw_group_diagonal_eq_mask colTriangle cols (by decide)]
    exact basisTensor_eq_maskDiagonal_mul rows cols pairTerm (fun _ ↦ Equiv.refl _) (fun _ _ _ ↦ rfl)
  apply ofRaw_le_iff.mp
  rw [ofRaw_mul, ← hprod]
  apply ofRaw_le_iff.mpr
  apply (Crossing.restriction_basisTensor_iff (pairTerm (O := O) (I := I)) _).mpr
  let G := (phaseRaw M).group Fin.castSucc
  let mat : ∀ j, G.Leg j → PairLeg O I j → K := five
    (fun r y ↦ if r ⟨0,rfl⟩ = y.1 (by decide) then 1 else 0)
    (fun r y ↦ if r ⟨1,rfl⟩ = y.2 (by decide) then 1 else 0)
    (fun r y ↦ if r ⟨2,rfl⟩ = y.1 (by decide) then 1 else 0)
    (fun r y ↦ if r ⟨3,rfl⟩ = y.2 (by decide) then 1 else 0)
    (fun _ y ↦ M (y.1 (by decide)) (y.2 (by decide)))
  refine ⟨mat, fun x ↦ ?_⟩
  let u : O := x 0 ⟨0,rfl⟩
  let v : I := x 1 ⟨1,rfl⟩
  let u' : O := x 2 ⟨2,rfl⟩
  let v' : I := x 3 ⟨3,rfl⟩
  change (phaseRaw M).coeff (fun i ↦ x i.castSucc ⟨i,rfl⟩) = _
  apply (phaseRaw_coeff M (fun i ↦ x i.castSucc ⟨i,rfl⟩)).trans
  change phaseEntry M u v u' v' = _
  rw [Fintype.sum_prod_type]
  rw [← phaseEntry_common_labels]
  apply Finset.sum_congr rfl
  intro o _
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change _ = (if u = o then 1 else 0) * ((if v = i then 1 else 0) *
    ((if u' = o then 1 else 0) * ((if v' = i then 1 else 0) * M o i)))
  ring

private theorem triangle_diagonal_ne_zero (A : Type) [Fintype A] [Nonempty A] :
    (Raw.diagonal (Fin 3) K A).coeff ≠ 0 := by
  intro h
  have hh := congrFun h (fun _ ↦ Classical.arbitrary A)
  change (Raw.diagonal (Fin 3) K A).coeff _ = 0 at hh
  rw [Raw.diagonal_coeff_at (0 : Fin 3)] at hh
  simp at hh

/-- Sharing the two labels over triangles meeting at the origin yields the
common-label upper bound, also when some of the terminal positions coincide. -/
theorem phaseCommonLabel_le (P : SpectralPlacementPrices K Plane)
    (hflat : ∀ (S : Finset Plane) (hS : S.Nonempty), P.diagonal S = meanWidth S hS)
    (M : Matrix O I K) (hcard : Fintype.card I = Fintype.card O) (x : Fin 4 → Plane) :
    fourierPhasePrice P M x ≤ Real.logb 2 (Fintype.card O) / 2 *
      (dist (x 0) (x 2) + ‖x 0‖ + ‖x 2‖ + dist (x 1) (x 3) + ‖x 1‖ + ‖x 3‖) := by
  by_cases hn : Fintype.card O = 0
  · have hM : M = 0 := funext fun o ↦ (Fintype.card_eq_zero_iff.mp hn).false o |>.elim
    have hzero : (phaseRaw M).coeff = 0 := not_not.mp fun h ↦ phaseRaw_coeff_ne_zero.mp h hM
    simp [fourierPhasePrice, hn, P.zero_tensor _ hzero]
  let : Nonempty O := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn)
  let : Nonempty I := Fintype.card_pos_iff.mp (by rw [hcard]; exact Nat.pos_of_ne_zero hn)
  let sites : Fin 5 → Plane := Fin.lastCases 0 x
  have hsite : sites ∘ Fin.castSucc = x := by funext i; simp [sites]
  have hrow : sites ∘ rowTriangle = ![x 0,x 2,0] := by funext i; fin_cases i <;> rfl
  have hcol : sites ∘ colTriangle = ![x 1,x 3,0] := by funext i; fin_cases i <;> rfl
  have hr := ((Raw.diagonal (Fin 3) K O).group_ne_zero_iff rowTriangle).2 (triangle_diagonal_ne_zero O)
  have hc := ((Raw.diagonal (Fin 3) K I).group_ne_zero_iff colTriangle).2 (triangle_diagonal_ne_zero I)
  have h := placed_price_mono P sites (phase_restricts_triangle_labels M)
  rw [placed_price_mul P sites _ _ hr hc, ← P.group, ← P.group, ← P.group,
    hsite, hrow, hcol, triangle_label_price P hflat, triangle_label_price P hflat, hcard] at h
  simp only [dist_zero_right] at h
  exact h.trans_eq (by ring)

end

end

end FiniteFourier
end LinearAlgebra
end OAI
