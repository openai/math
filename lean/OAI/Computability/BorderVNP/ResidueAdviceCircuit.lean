import OAI.Computability.BorderVNP.BranchTableConstruction
import OAI.Computability.BorderVNP.ResidueEntryCircuitTable
import OAI.Computability.BorderVNP.HittingSetHasseCircuit

/-!
# Circuits for the actual branch equations

The polynomials used by the residue reader are the full cleared equations
produced by the chosen `CurveAdvice`. Their weighted sum of all degree-component
coordinates is computed by one shared grammar table. The coordinate pins and
affine deformation add only linearly many gates. This is a formal-polynomial
identity over the advice field, including when that field is finite.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open VPVNP ParseTable MvPolynomial
open scoped BigOperators Classical

variable {E : Type*} [Field E]

/-- Bound on the gate count of a selected full affine row, including its chart pins. -/
def adviceGateBudget (v k s : ℕ) :=
  tableGateBudget v (v+s+1) (k+1) + 2*(parameterCount v k s + 1) + 7

private theorem numbered_weightedTable (v k s : ℕ) (a : E)
    [Fintype (DegreeMonomial (Fin v) (k+1))] :
    (∑ i : DegreeMonomial (Fin v) (k+1), numberedTable E v k s i * C (a ^ digitExponent (k+2) i.val)) =
      weightedTable v (Fintype.card (Fin v)+s+1) (k+1) (Fintype.equivFin _)
        (fun i => a^((k+2)^i.val)) (Fin.last k) 0 := by
  rw [weightedTable_eq_coordinateSum]
  let P := (universalGrammar (Fin v) (State (Fin v) s) (k+1)).eval (Fin.last k) 0
  have hh : P.IsHomogeneous (k+1) := (universalGrammar ..).eval_isHomogeneous (Fin.last k) 0
  let inc (i : P.support) : DegreeMonomial (Fin v) (k+1) :=
    ⟨i.val, Classical.byContradiction fun h => (mem_support_iff.mp i.property) (hh.coeff_eq_zero h)⟩
  have hin : Function.Injective inc := fun i j he => Subtype.ext (congrArg (fun a : DegreeMonomial (Fin v) (k+1) => a.val) he)
  change _ = ∑ i ∈ P.support, rename _ (map (Int.castRingHom E) (P.coeff i)) * C _
  rw [← Finset.sum_coe_sort P.support]
  symm
  apply Fintype.sum_of_injective inc hin
  · intro i hi
    have h : i.val ∉ P.support := fun hm => hi ⟨⟨i.val,hm⟩,Subtype.ext rfl⟩
    change rename _ (map (Int.castRingHom E) (P.coeff i.val)) * C _ = 0
    rw [notMem_support_iff.mp h, map_zero, map_zero, zero_mul]
  · intro i
    rfl

private theorem chartDen_size {h : ℕ} (k : Option (Fin h)) :
    circuitSize (affineChartDen (K := E) k) = 0 := by
  cases k with
  | none => exact circuitSize_C (σ := Fin h) (1 : E)
  | some j => exact circuitSize_X j

private theorem chartRename_size {h : ℕ} (a : MvPolynomial (Fin h) E) :
    circuitSize (rename some a) ≤ circuitSize a := by
  rw [rename_eq_aeval]
  exact circuitSize_projection_le (fun j => Sum.inl (some j)) a

/-- The circuit bound for the literal equation of Proposition 9.2, not just its
evaluation on the finite coefficient field. -/
theorem CurveAdvice.equations_circuitSize (v k s : ℕ) [Fintype (DegreeMonomial (Fin v) (k+1))]
    (advice : CurveAdvice E (parameterCount v k s)) (c : DegreeMonomial (Fin v) (k+1) → E)
    (B : ℕ) (i : Fin (parameterCount v k s)) :
    circuitSize (advice.equations (numberedTable E v k s) c
      (fun ν => digitExponent (k+2) ν.val) B i) ≤ adviceGateBudget v k s := by
  let h := parameterCount v k s
  let a := advice.scalar i
  let out := weightedTable v (Fintype.card (Fin v)+s+1) (k+1) (Fintype.equivFin _)
    (fun j => a^((k+2)^j.val)) (Fin.last k) 0
  let den : MvPolynomial (Fin h) E := affineChartDen advice.chart
  let num : MvPolynomial (Fin h) E := affineChartNum advice.chart i
  let e (ν : DegreeMonomial (Fin v) (k+1)) := digitExponent (k+2) ν.val
  let offset := weightedOffset c advice.pins advice.pinValue e B a
  let term (j : advice.pins) : MvPolynomial (Fin h) E :=
    affineChartDen ((_root_.finSuccEquiv h) j.val) * C (a ^ residualExponent e B advice.pins (.inr j))
  have hout : circuitSize out ≤ tableGateBudget v (v+s+1) (k+1) := by
    simpa only [Fintype.card_fin] using circuitSize_weightedTable
      (n := k+1) (h := Fintype.card (Fin v)+s+1) (Fintype.equivFin _) (fun j => a^((k+2)^j.val))
      (Fin.last k) 0
  have hd : circuitSize den = 0 := chartDen_size _
  have hn : circuitSize num = 0 := chartDen_size _
  have hb : circuitSize (∑ j, term j) ≤ (h+1)*2 := by
    refine (HittingSet.circuitSize_finsetSum_le Finset.univ term 1 (fun j _ => ?_)).trans ?_
    · dsimp only [term]
      exact (circuitSize_binOp_le .mul ..).trans (by rw [chartDen_size, circuitSize_C])
    · rw [Finset.card_univ, Fintype.card_coe]
      exact Nat.mul_le_mul_right 2 (by simpa only [Fintype.card_fin] using advice.pins.card_le_univ)
  have ho := circuitSize_binOp_le .sub out (C offset)
  have hdo := circuitSize_binOp_le .mul den (out - C offset)
  have hrow := (chartRename_size _).trans (circuitSize_binOp_le .add (den*(out-C offset)) (∑ j, term j))
  have ht := circuitSize_binOp_le .mul (C (advice.target i)) den
  have hsub := (chartRename_size _).trans (circuitSize_binOp_le .sub num (C (advice.target i)*den))
  have hp := circuitSize_binOp_le .mul (X (none : Option (Fin h)))
    (rename some (num - C (advice.target i) * den))
  have hsum := circuitSize_binOp_le .add (rename some (den*(out-C offset) + ∑ j, term j))
    (X none * rename some (num - C (advice.target i)*den))
  rw [CurveAdvice.equations, affineEquation, affineSlice_weighted, numbered_weightedTable]
  change circuitSize (rename some (den*(out-C offset) + ∑ j, term j) +
    X none * rename some (num - C (advice.target i)*den)) ≤ _
  simp only [BinOp.apply, circuitSize_C, circuitSize_X, hd, hn] at ho hdo hrow ht hsub hp hsum
  unfold adviceGateBudget
  dsimp only [h] at *
  omega

end Branch

end BorderVNP
end Computability
end OAI
