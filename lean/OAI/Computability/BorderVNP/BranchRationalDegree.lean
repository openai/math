import OAI.Computability.BorderVNP.BranchCone
import OAI.Computability.BorderVNP.BranchDegree

/-!
# Separating equations for rational charts

Polynomial cone normalization reduces effective separation for rational parametrizations
with a common denominator to effective separation for a polynomial map. The degree
bound depends on the parameter dimension and degrees, independently of the number of
output coordinates.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial VPVNP.RadicalCertificate

variable {K ι : Type*} [Field K] [Infinite K] [Fintype ι] {h : ℕ}

omit [Infinite K] in
private theorem eval_generic (b : MvPolynomial (Fin h) K) :
    eval₂ (algebraMap K (ParameterField (Fin h) K))
      (fun j => algebraMap _ _ (X j : MvPolynomial (Fin h) K)) b = algebraMap _ _ b := by
  let inc := algebraMap (MvPolynomial (Fin h) K) (ParameterField (Fin h) K)
  change eval₂Hom _ (fun j => inc (X j)) b = inc b
  exact RingHom.congr_fun (MvPolynomial.ringHom_ext
    (fun r => by simp [inc, IsScalarTower.algebraMap_apply K (MvPolynomial (Fin h) K) (ParameterField (Fin h) K)])
    (fun j => by simp)) b

omit [Fintype ι] in
private theorem cone_zero_of_relation (b : MvPolynomial (Fin h) K)
    (a : ι → MvPolynomial (Fin h) K) (hb : b ≠ 0) (p : MvPolynomial ι K)
    (hp : aeval (fun i => algebraMap _ (ParameterField (Fin h) K) (a i) /
      algebraMap _ _ b) p = 0) :
    aeval (coneTable b a) (coneEquation p) = 0 := by
  let L := ParameterField (Fin h) K
  let inc := algebraMap (MvPolynomial (Fin h) K) L
  have hi : Function.Injective inc := IsFractionRing.injective _ _
  have hscalar : inc.comp C = algebraMap K L := by
    ext k; exact (IsScalarTower.algebraMap_apply K (MvPolynomial (Fin h) K) L k).symm
  have hden : inc b ≠ 0 := (map_ne_zero_iff inc hi).mpr hb
  have hbase : aeval (fun j : Option ι => j.elim b a) (coneEquation p) = 0 := by
    apply hi
    rw [map_zero, MvPolynomial.map_aeval]
    change eval₂Hom (inc.comp C) (fun i => inc (i.elim b a)) (coneEquation p) = 0
    have hc (j : Option ι) : inc (j.elim b a) = j.elim (inc b) (inc ∘ a) := by cases j <;> rfl
    simp_rw [hc]
    rw [hscalar, coe_eval₂Hom, eval_coneEquation _ _ _ _ hden]
    change inc b ^ p.totalDegree * aeval (fun i => inc (a i) / inc b) p = 0
    rw [hp, mul_zero]
  apply MvPolynomial.funext
  intro y
  let s := y 0
  let x := fun j : Fin h => y j.succ
  have hy : y = Fin.cons s x := (Fin.cons_self_tail y).symm
  change eval₂ (RingHom.id K) y _ = _
  rw [hy, eval_coneTable]
  have hsc := eval_coneEquation_scale (RingHom.id K) p s
    (fun j : Option ι => eval₂ (RingHom.id K) x (j.elim b a))
  rw [hsc]
  have hx := congrArg (eval x) hbase
  rw [map_zero, MvPolynomial.map_aeval] at hx
  have hid : (eval x).comp (algebraMap K (MvPolynomial (Fin h) K)) = RingHom.id K := by
    ext k; simp
  rw [hid] at hx
  change eval₂ (RingHom.id K) (fun i => eval₂ (RingHom.id K) x (i.elim b a)) (coneEquation p) = 0 at hx
  rw [hx, mul_zero, map_zero]

/-- Effective separation of a rational image from a point, over an arbitrary infinite
field. The input relation may have arbitrary degree. -/
theorem bounded_rational_separator (b : MvPolynomial (Fin h) K)
    (a : ι → MvPolynomial (Fin h) K) (c : ι → K) {d : ℕ} (hb : b ≠ 0)
    (hbd : b.totalDegree ≤ d) (had : ∀ i, (a i).totalDegree ≤ d)
    (p : MvPolynomial ι K)
    (hp : aeval (fun i => algebraMap _ (ParameterField (Fin h) K) (a i) /
      algebraMap _ _ b) p = 0) (hc : eval c p ≠ 0) :
    ∃ Q : MvPolynomial ι K, Q.totalDegree ≤ 2 * perronSimplexBound (h+2) (d+2) ∧
      aeval (fun i => algebraMap _ (ParameterField (Fin h) K) (a i) / algebraMap _ _ b) Q = 0 ∧
      eval c Q = 1 := by
  classical
  let L := ParameterField (Fin h) K
  let inc := algebraMap (MvPolynomial (Fin h) K) L
  have hden : inc b ≠ 0 := (map_ne_zero_iff inc (IsFractionRing.injective _ _)).mpr hb
  have he : eval (fun j : Option ι => j.elim 1 c) (coneEquation p) ≠ 0 := by
    change eval₂ (RingHom.id K) _ _ ≠ 0
    rw [eval_coneEquation _ _ _ _ one_ne_zero]
    simpa using hc
  obtain ⟨U, hU, hu, hpoint⟩ := bounded_separating_relation (coneTable b a)
    (fun j : Option ι => j.elim 1 c) (coneTable_degree b a hbd had) (coneEquation p)
    (cone_zero_of_relation b a hb p hp) he
  let u : Option ι → MvPolynomial ι K := fun j => j.elim 1 X
  refine ⟨aeval u U, (totalDegree_affine_substitution U u (fun j => by cases j <;> simp [u])).trans hU, ?_, ?_⟩
  · let rr (i : ι) := inc (a i) / inc b
    let x := fun j : Fin h => inc (X j)
    have hz := congrArg (eval₂Hom (algebraMap K L) (Fin.cons (inc b)⁻¹ x)) hu
    change eval₂ (algebraMap K L) _ (aeval (coneTable b a) U) = _ at hz
    rw [eval_coneTable, map_zero] at hz
    simp_rw [show ∀ f : MvPolynomial (Fin h) K, eval₂ (algebraMap K L) x f = inc f from eval_generic] at hz
    change aeval rr (aeval u U) = 0
    rw [← AlgHom.comp_apply, comp_aeval]
    change eval₂ (algebraMap K L) _ U = 0
    convert hz using 2
    funext j
    cases j with
    | none => simpa only [Option.elim, u, map_one] using (inv_mul_cancel₀ hden).symm
    | some i => simp [u, rr, div_eq_mul_inv, mul_comm]
  · rw [MvPolynomial.map_aeval]
    have e : (eval c).comp (algebraMap K (MvPolynomial ι K)) = RingHom.id K := by ext k; simp
    rw [e]
    have hs : (fun i => eval c (u i)) = fun j : Option ι => j.elim 1 c := by
      funext j; cases j <;> simp [u]
    rw [hs]
    exact hpoint

end Branch

end BorderVNP
end Computability
end OAI
