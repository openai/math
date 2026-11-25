import OAI.Computability.BorderVNP.BranchParseFamily
import OAI.Computability.BorderVNP.BranchWeightedAffineEquation
import OAI.Computability.BorderVNP.BranchSliceTable

/-! # The numbered universal table in the affine-equation reader

The chart variables use the enumeration of production labels of the universal grammar.
For every assignment to these variables, the degree-component sum in the weighted
affine equation is exactly one dynamic-programming table entry. All degree-component
monomials are accounted for, even when a coefficient specializes to zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial VPVNP ParseTable

variable {E R : Type*} [Field E] [Field R] {v k s : ℕ}

/-- Read grammar production labels from the numbered parameter vector. -/
noncomputable def numberedGrammar (x : Fin (parameterCount v k s) → R) :
    ParseGrammar R (Fin v) (State (Fin v) s) (k+1) where
  terminal j i := x (Fintype.equivFin _ (.inl (j,i)))
  binary d j r l u := x (Fintype.equivFin _ (.inr ⟨d,j,r,l,u⟩))

/-- Evaluating any one coordinate of the numbered table reads the corresponding
coefficient of the specialized grammar polynomial. -/
theorem eval_numberedTable (f : E →+* R) (x : Fin (parameterCount v k s) → R)
    (ν : DegreeMonomial (Fin v) (k+1)) :
    eval₂Hom f x (numberedTable E v k s ν) =
      ((numberedGrammar x).eval (Fin.last k) 0).coeff ν.val := by
  let G := numberedGrammar x
  have he : G.labelValue = x ∘ Fintype.equivFin _ := by
    funext j
    rcases j with ⟨j,i⟩ | ⟨d,j,r,l,u⟩ <;> rfl
  rw [numberedTable, coe_eval₂Hom, eval₂_rename, eval₂_map,
    show f.comp (Int.castRingHom E) = Int.castRingHom R from Subsingleton.elim .., ← he]
  exact G.specialize_coefficient _ _ _

/-- The full weighted sum of the numbered table's coordinates is one entry in the
shared layer-by-layer table, evaluated at the indicated powers of the slice scalar. -/
theorem numberedTable_weighted [Fintype (DegreeMonomial (Fin v) (k+1))] (f : E →+* R)
    (x : Fin (parameterCount v k s) → R) (a : R) :
    ∑ ν : DegreeMonomial (Fin v) (k+1), eval₂Hom f x (numberedTable E v k s ν) *
      a ^ digitExponent (k+2) ν.val =
    (tableRows (numberedGrammar x) (fun i => a^((k+2)^i.val)) (k+1) le_rfl)[k][0] := by
  classical
  rw [show (tableRows (numberedGrammar x) (fun i => a^((k+2)^i.val)) (k+1) le_rfl)[k][0] =
      eval (fun i => a^((k+2)^i.val)) ((numberedGrammar x).eval (Fin.last k) 0) from
    tableRows_correct _ _ _ _ (Fin.last k) 0, eval_at_digit_powers]
  simp_rw [eval_numberedTable]
  let p := (numberedGrammar x).eval (Fin.last k) 0
  have hh : p.IsHomogeneous (k+1) := (numberedGrammar x).eval_isHomogeneous (Fin.last k) 0
  let inc (i : p.support) : DegreeMonomial (Fin v) (k+1) :=
    ⟨i.val, Classical.byContradiction fun he => (mem_support_iff.mp i.property) (hh.coeff_eq_zero he)⟩
  have hi : Function.Injective inc := fun i j h => Subtype.ext (congrArg (fun q : DegreeMonomial (Fin v) (k+1) => q.val) h)
  change _ = ∑ i ∈ p.support, p.coeff i * a ^ digitExponent (k+2) i
  rw [← Finset.sum_coe_sort p.support]
  symm
  apply Fintype.sum_of_injective inc hi
  · intro ν hn
    have h : ν.val ∉ p.support := fun h => hn ⟨⟨ν.val, h⟩, Subtype.ext rfl⟩
    rw [notMem_support_iff.mp h, zero_mul]
  · intro i
    rfl

/-- Evaluation of the selected branch equation for the actual universal numbered
coefficient map. The only access to the output coefficient vector is via its scalar offset. -/
theorem eval_numbered_affineEquation [Fintype (DegreeMonomial (Fin v) (k+1))] (f : E →+* R)
    (chart : Option (Fin (parameterCount v k s))) (c : DegreeMonomial (Fin v) (k+1) → E)
    (pins : Finset (Fin (parameterCount v k s + 1))) (p : Fin (parameterCount v k s + 1) → E)
    (a target : Fin (parameterCount v k s) → E) (i : Fin (parameterCount v k s)) (t : R)
    (x : Fin (parameterCount v k s) → R) :
    let e := fun ν : DegreeMonomial (Fin v) (k+1) => digitExponent (k+2) ν.val
    let B := (k+2)^v
    let val := eval₂Hom f x
    let den := val (affineChartDen (K := E) chart)
    let row := fun j => graphSliceRow c pins p e B (a j)
    eval₂Hom f (fun o : Option (Fin (parameterCount v k s)) => o.elim t x)
      (affineEquation (numberedTable E v k s) chart row target i) =
      den * ((tableRows (numberedGrammar x) (fun j => (f (a i))^((k+2)^j.val)) (k+1) le_rfl)[k][0] -
        f (weightedOffset c pins p e B (a i))) +
      (∑ j : pins, val (affineChartDen ((_root_.finSuccEquiv _) j.val)) *
        (f (a i))^(residualExponent e B pins (.inr j))) +
      t * (val (affineChartNum chart i) - f (target i) * den) := by
  intro e B val den row
  rw [show eval₂Hom f (fun o : Option (Fin (parameterCount v k s)) => o.elim t x)
      (affineEquation (numberedTable E v k s) chart row target i) = _ from
    eval_weighted_affineEquation f _ chart c pins p e B a target i t x]
  rw [numberedTable_weighted f x]

end Branch

end BorderVNP
end Computability
end OAI
