import OAI.Computability.BorderVNP.BranchGrid
import OAI.Computability.BorderVNP.BranchIncidenceCount
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Roots

/-!
# Choosing all weighted slices at once

For each possible highest nonzero coefficient of the weighted equations and each
graph coordinate, an incidence relation gives a nonzero equation in that coordinate
and the slice scalars. One nonzero coefficient of each such equation suffices: away
from its zeros every coordinate has only finitely many choices. This produces a finite
intersection with precisely as many slices as there are parameters.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch.Incidence

open MvPolynomial

variable {E K I S : Type*} [Field E] [Fintype E] [Field K] [Fintype I] [Fintype S] {h : ℕ}

/-- Choose a grid point at which all the relations retain a nonzero univariate
coefficient. The resulting coordinate-root conditions allow only finitely many
graph points in each stratum. -/
theorem finite_coordinate_strata (embed : E →+* K) (W : S → I → MvPolynomial (Fin (h+1)) K)
    (D : ℕ) (hne : ∀ r i, W r i ≠ 0) (hdeg : ∀ r i, (W r i).totalDegree ≤ D)
    (hsize : Fintype.card S * Fintype.card I * D < Fintype.card E) :
    ∃ a : Fin h → E, (⋃ r : S, {v : I → K |
      ∀ i, eval (Fin.cons (v i) (embed ∘ a)) (W r i) = 0}).Finite := by
  classical
  let U (j : S × I) := finSuccEquiv K h (W j.1 j.2)
  have hU (j) : U j ≠ 0 := (map_ne_zero_iff _ (finSuccEquiv K h).injective).mpr (hne j.1 j.2)
  let c (j : S × I) := (U j).leadingCoeff
  have hc (j) : c j ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr (hU j)
  have hd (j) : (c j).totalDegree ≤ D := by
    have hj := totalDegree_coeff_finSuccEquiv_add_le (W j.1 j.2) (U j).natDegree (hc j)
    exact (Nat.le_add_right _ _).trans (hj.trans (hdeg ..))
  let en := (Fintype.equivFin (S × I)).symm
  have hs : (∑ j, (c (en j)).totalDegree) < Fintype.card E := by
    apply lt_of_le_of_lt (Finset.sum_le_sum (fun j _ => hd (en j)))
    simpa [Fintype.card_prod] using hsize
  obtain ⟨a, ha⟩ := exists_constants_avoiding embed (fun j => c (en j)) (fun j => hc _) hs
  refine ⟨a, Set.finite_iUnion fun r => ?_⟩
  let Q (i : I) := Polynomial.map (eval (embed ∘ a)) (U (r,i))
  have hQ (i) : Q i ≠ 0 := by
    intro hz
    have he := congrArg (fun P : Polynomial K => P.coeff (U (r,i)).natDegree) hz
    apply ha (en.symm (r,i))
    rw [en.apply_symm_apply]
    change eval (embed ∘ a) ((U (r,i)).coeff (U (r,i)).natDegree) = 0
    simpa only [Q, Polynomial.coeff_map, Polynomial.coeff_zero] using he
  let roots (i : I) := {x : K | (Q i).IsRoot x}
  have (i : I) : Finite (roots i) := Set.finite_coe_iff.mpr <| Polynomial.finite_setOfPred_isRoot (hQ i)
  let V := {v : I → K | ∀ i, eval (Fin.cons (v i) (embed ∘ a)) (W r i) = 0}
  let f (v : V) (i : I) : roots i :=
    ⟨v.val i, by change (Q i).eval (v.val i) = 0; simpa only [eval_eq_eval_mv_eval'] using v.prop i⟩
  apply Set.finite_coe_iff.mp
  exact Finite.of_injective f (fun v w e => Subtype.ext (funext fun i => congrArg Subtype.val (congrFun e i)))

omit [Fintype I] in
/-- At a point outside the base fiber, the weighted polynomial has a unique
positive top degree whenever the selected scalar tuple consists of roots.
Truncating there gives exactly the equations used by the incidence algebra. -/
theorem top_stratum_of_roots {B : ℕ} (F : Polynomial (MvPolynomial I K)) (v : I → K)
    (a : Fin h → K) (hh : 0 < h) (hF : F.natDegree ≤ B)
    (hv : F.map (eval v) ≠ 0) (hroot : ∀ j, (F.map (eval v)).eval (a j) = 0) :
    ∃ r : Fin B, eval v (F.coeff (r.val+1)) ≠ 0 ∧
      ∀ j, eval v (F.coeff (r.val+1)) * (a j)^(r.val+1) +
        ∑ i : Fin (r.val+1), eval v (F.coeff i.val) * (a j)^i.val = 0 := by
  let P := F.map (eval v)
  have hpos : P.natDegree ≠ 0 := by
    intro hz
    have h := hroot ⟨0, hh⟩
    change P.eval _ = 0 at h
    rw [Polynomial.eq_C_of_natDegree_eq_zero hz, Polynomial.eval_C] at h
    exact hv ((Polynomial.eq_C_of_natDegree_eq_zero hz).trans (by simp [h]))
  have hle : P.natDegree ≤ B := (Polynomial.natDegree_map_le ..).trans hF
  let r : Fin B := ⟨P.natDegree-1, by omega⟩
  have he : r.val+1 = P.natDegree := by dsimp [r]; omega
  refine ⟨r, ?_, fun j => ?_⟩
  · rw [he, ← Polynomial.coeff_map]
    exact Polynomial.leadingCoeff_ne_zero.mpr hv
  · have hz := hroot j
    change P.eval (a j) = 0 at hz
    rw [Polynomial.eval_eq_sum_range, ← he, Finset.sum_range_succ] at hz
    rw [← Fin.sum_univ_eq_sum_range] at hz
    simpa only [P, Polynomial.coeff_map, add_comm] using hz

end Branch.Incidence

end BorderVNP
end Computability
end OAI
