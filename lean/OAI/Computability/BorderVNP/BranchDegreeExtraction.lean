import OAI.Computability.BorderVNP.BranchDegreeGraph

/-! # Extracting a bounded separating equation from a monic relation

Expand the relation in the extra graph parameter and take the coefficient indexed by its
monic degree. At the target every scaled difference vanishes, so this coefficient is one.
At the parameter image the whole relation vanishes, so the coefficient is identically zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial

variable {I K : Type*} [Field K] [Fintype I] {h m : ℕ}

private theorem split_rename (p : MvPolynomial (Fin h) K) :
    finSuccEquiv K h (rename Fin.succ p) = Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C k => simp [finSuccEquiv_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, finSuccEquiv_X_succ]

omit [Fintype I] in
private theorem split_realization (Y : I → MvPolynomial (Fin h) K) (p : MvPolynomial (Option I) K) :
    (optionEquivLeft K I p).map (aeval Y).toRingHom =
      finSuccEquiv K h (liftParametrization Y p) := by
  induction p using MvPolynomial.induction_on with
  | C k => simp [liftParametrization, finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.map_mul, hp]
    congr 1
    cases i <;> simp [liftParametrization, finSuccEquiv_X_zero, split_rename]

private noncomputable def targetMap (c : I → K) : MvPolynomial (Option I) K →+* Polynomial K :=
  (Polynomial.mapRingHom (eval c)).comp (optionEquivLeft K I).toRingHom

omit [Fintype I] in
private theorem target_coordinates (c : I → K) (i : I ⊕ I) :
    targetMap c (differenceCoordinates c i) = Polynomial.C (Sum.elim c (fun _ => 0) i) := by
  cases i <;> simp [targetMap, differenceCoordinates, Polynomial.coe_mapRingHom]

private theorem target_sum (c : I → K) (a : I ⊕ I → K) :
    targetMap c (∑ i, a i • differenceCoordinates c i) =
      Polynomial.C (∑ i, a i * Sum.elim c (fun _ => 0) i) := by
  simp only [smul_eq_C_mul, map_sum, map_mul, target_coordinates]
  apply Finset.sum_congr rfl
  intro i _
  simp [targetMap, Polynomial.coe_mapRingHom]

omit [Fintype I] in
private theorem target_relation (c : I → K) (Q : Fin m → MvPolynomial (Option I) K)
    (b : Fin m → K) (hb : ∀ i, targetMap c (Q i) = Polynomial.C (b i))
    (p : MvPolynomial (Fin (m+1)) K) :
    targetMap c (aeval (Fin.cons (X none) Q) p) = (finSuccEquiv K m p).map (eval b) := by
  induction p using MvPolynomial.induction_on with
  | C k => simp [targetMap, finSuccEquiv_apply, Polynomial.coe_mapRingHom]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.map_mul, hp, aeval_X]
    congr 1
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [targetMap, finSuccEquiv_X_zero, Polynomial.coe_mapRingHom]
    · simpa [finSuccEquiv_X_succ] using hb k

/-- A monic relation in linear combinations of the realized graph coordinates gives a
separating equation of at most twice its total degree, taking value exactly one at the target. -/
theorem extract_separator (Y : I → MvPolynomial (Fin h) K) (c : I → K)
    (Q : Fin m → MvPolynomial (Fin (h+1)) K) (U : MvPolynomial (Fin (m+1)) K)
    (hQ : ∀ i, Q i ∈ Submodule.span K (Set.range (realizedDifferences Y c)))
    (hmon : (finSuccEquiv K m U).Monic) (hz : aeval (Fin.cons (X 0) Q) U = 0) :
    ∃ f : MvPolynomial I K, f.totalDegree ≤ 2*U.totalDegree ∧ aeval Y f = 0 ∧ eval c f = 1 := by
  classical
  choose a ha using fun i => (Submodule.mem_span_range_iff_exists_fun K).mp (hQ i)
  let Q' (j : Fin m) := ∑ i, a j i • differenceCoordinates c i
  let S : Fin (m+1) → MvPolynomial (Option I) K := Fin.cons (X none) Q'
  let P := aeval S U
  let k := (finSuccEquiv K m U).natDegree
  have hQ' (j) : liftParametrization Y (Q' j) = Q j := by
    simpa only [Q', map_sum, map_smul, realizedDifferences, Function.comp_apply] using ha j
  have hS : (fun i => liftParametrization Y (S i)) = Fin.cons (X 0) Q := by
    funext i
    refine Fin.cases ?_ (fun j => hQ' j) i
    simp [S, liftParametrization]
  have hP : liftParametrization Y P = 0 := by
    change liftParametrization Y (aeval S U) = 0
    rw [← AlgHom.comp_apply, comp_aeval, hS, hz]
  let b (j : Fin m) := ∑ i, a j i * Sum.elim c (fun _ => 0) i
  have hb (j) : targetMap c (Q' j) = Polynomial.C (b j) := target_sum c (a j)
  have hPdeg : P.totalDegree ≤ 2*U.totalDegree := by
    apply substitute_degree
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [S]
    · exact totalDegree_finsetSum_le fun u _ =>
        (totalDegree_smul_le ..).trans (differenceCoordinates_degree c u)
  refine ⟨(optionEquivLeft K I P).coeff k, (totalDegree_coeff_optionEquivLeft_le K I P k).trans hPdeg,
    ?_, ?_⟩
  · have h := congrArg (fun p => Polynomial.coeff p k) (split_realization Y P)
    rw [hP, map_zero, Polynomial.coeff_zero, Polynomial.coeff_map] at h
    exact h
  · have h := congrArg (fun p => Polynomial.coeff p k) (target_relation c Q' b hb U)
    change ((optionEquivLeft K I P).map (eval c)).coeff k =
      ((finSuccEquiv K m U).map (eval b)).coeff k at h
    simpa [Polynomial.coeff_map, k, hmon.coeff_natDegree] using h

end Branch

end BorderVNP
end Computability
end OAI
