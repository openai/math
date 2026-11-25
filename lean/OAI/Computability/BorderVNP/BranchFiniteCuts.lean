import OAI.Computability.BorderVNP.BranchMixture
import OAI.Computability.BorderVNP.BranchIncidenceBits

/-!
# The retained point and the short weighted slices of Proposition 9.2

The same finite grid supplies the hyperplane constants and all weighted-slice scalars.
The field of definition of the original coefficients is preserved. The point on the
graph and the bounded equations used to prove the existence of the cuts need not be
encoded in the advice.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial VPVNP.SliceGeometry

variable {E₀ K I : Type*} [Field E₀] [Fintype E₀] [Field K] [IsAlgClosed K] [Algebra E₀ K]
  [Fintype I] {h : ℕ}

/-- Each output has its assigned digit exponent. The extra coordinate equations use the
successive larger powers, as in the second sum of the manuscript's `Dₐ`. -/
noncomputable def residualExponent (e : I → ℕ) (B : ℕ) (s : Finset (Fin (h+1))) : I ⊕ s → ℕ :=
  Sum.elim e (fun j => B + ((Fintype.equivFin s) j).val + 1)

omit [Fintype I] in
private theorem exponent_inj (e : I → ℕ) (B : ℕ) (he : Function.Injective e) (hB : ∀ j, e j < B)
    (s : Finset (Fin (h+1))) : Function.Injective (residualExponent e B s) := by
  intro x y eq
  cases x with
  | inl i =>
    cases y with
    | inl j => exact congrArg Sum.inl (he eq)
    | inr j => change e i = B + _ + 1 at eq; have := hB i; omega
  | inr i =>
    cases y with
    | inl j => change B + _ + 1 = e j at eq; have := hB j; omega
    | inr j =>
      apply congrArg Sum.inr
      apply (Fintype.equivFin s).injective
      apply Fin.ext
      change B + _ + 1 = B + _ + 1 at eq
      omega

/-- The actual slice on graph coordinates, with scalar `a` and coordinate pins `p`. -/
noncomputable def graphSliceRow {E : Type*} [Field E] (c : I → E) (s : Finset (Fin (h+1)))
    (p : Fin (h+1) → E) (e : I → ℕ) (B : ℕ) (a : E) : MvPolynomial (Option (Fin h) ⊕ I) E :=
  ∑ j, fiberResiduals c s p j * C (a ^ residualExponent e B s j)

/-- Every actual weighted row is affine in the graph coordinates. -/
theorem graphSliceRow_degree {E : Type*} [Field E] (c : I → E) (s : Finset (Fin (h+1)))
    (p : Fin (h+1) → E) (e : I → ℕ) (B : ℕ) (a : E) :
    (graphSliceRow c s p e B a).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro j _
  simpa only [totalDegree_C, add_zero] using
    (totalDegree_mul (fiberResiduals c s p j) (C (a ^ residualExponent e B s j))).trans
      (Nat.add_le_add_right (fiberResiduals_degree c s p j) _)

omit [IsAlgClosed K] in
private theorem eval_row_map {E : Type*} [Field E] (i : E →+* K) (c : I → E)
    (s : Finset (Fin (h+1))) (p : Fin (h+1) → E) (e : I → ℕ) (B : ℕ) (a : E)
    (z : Option (Fin h) ⊕ I → K) :
    eval z (map i (graphSliceRow c s p e B a)) =
      ((weightedGraph (residualExponent e B s) (fiberResiduals (i ∘ c) s (i ∘ p))).map (eval z)).eval (i a) := by
  rw [eval_weightedGraph]
  simp only [graphSliceRow, map_sum, map_mul, map_C, eval_C, map_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  cases j <;> simp [fiberResiduals]

/-- Cardinality budget for the single field used for the hyperplanes and weighted rows. -/
def sliceGridBound (h d B n : ℕ) : ℕ :=
  max (fiberPinBound (h+1) (graphFiberDegree h d))
    (mixtureBound h (B+h+1) ((h+1)+n) (d+1))

/-- One finite extension, at most `h+1` coordinate pins and exactly `h` weighted rows
give a finite nonempty special fiber containing a point with the required outputs. -/
theorem exists_finite_slices (Y : I → MvPolynomial (Fin h) K) (c : I → E₀) (e : I → ℕ)
    (d B : ℕ) (hh : 0 < h) (hY : ∀ i, (Y i).totalDegree ≤ d)
    (he : Function.Injective e) (hB : ∀ i, e i < B)
    (hc : (algebraMap E₀ K) ∘ c ∈ imageClosure (Set.range (fun x : Fin h → K => fun i => eval x (Y i)))) :
    ∃ (k : Option (Fin h)) (E : IntermediateField E₀ K), Finite E ∧
      Nat.card E ≤ Fintype.card E₀ * max (sliceGridBound h d B (Fintype.card I)) 1 ∧
      homogeneousParameters (Fin h) K k ≠ 0 ∧
      ∃ (s : Finset (Fin (h+1))) (p : Fin (h+1) → E) (a : Fin h → E),
        let D := fun i => map E.subtype (graphSliceRow ((algebraMap E₀ E) ∘ c) s p e B (a i))
        let cut := {v ∈ zeroLocus K (RingHom.ker (graphChartMap Y k)) | ∀ i, eval v (D i) = 0}
        cut.Finite ∧ ∃ z, Sum.elim z ((algebraMap E₀ K) ∘ c) ∈ cut := by
  classical
  let ck := (algebraMap E₀ K) ∘ c
  obtain ⟨k, z, hk, _, hz⟩ := exists_graphChart_point Y ck hc
  obtain ⟨S, hS, hs⟩ := graphFiber_equations Y ck d hY k hk
  have hm : z ∘ (_root_.finSuccEquiv h) ∈ graphFiber Y ck k := by
    change Sum.elim ((z ∘ (_root_.finSuccEquiv h)) ∘ (_root_.finSuccEquiv h).symm) ck ∈ zeroLocus K _
    simpa [Function.comp_assoc] using hz
  have hv : graphFiber Y ck k = {x | ∀ q : S, eval x q.val = 0} := by simp [hs]
  obtain ⟨E, hE, hlo, hhi⟩ := exists_gridExtension E₀ K (sliceGridBound h d B (Fintype.card I))
  let := Fintype.ofFinite E
  rw [Nat.card_eq_fintype_card] at hlo
  have hgrid : fiberPinBound (h+1) (graphFiberDegree h d) < Fintype.card E := (le_max_left ..).trans_lt hlo
  rw [hv] at hm
  obtain ⟨s,p,hp0,hp,_⟩ := finite_fiber_by_subfield_pins (K := E) (le_max_left ..)
    (fun q : S => q.val) (fun q => hS _ q.property) ⟨_,hm⟩ hgrid
  rw [← hv] at hp0 hp
  let idx := residualExponent e B s
  let residual := fiberResiduals ck s (E.subtype ∘ p)
  let F := weightedGraph idx residual
  have hidx : Function.Injective idx := exponent_inj e B he hB s
  have hbound (j) : idx j ≤ B+h+1 := by
    cases j with
    | inl i => exact (hB i).le.trans (by omega)
    | inr i =>
      have hj := ((Fintype.equivFin s) i).isLt
      have hcard := s.card_le_univ
      simp only [Fintype.card_coe, Fintype.card_fin] at *
      change B + _ + 1 ≤ B+h+1; omega
  obtain ⟨hFd,hFc⟩ := weightedGraph_bounds idx hidx _ hbound residual (fun j => fiberResiduals_degree ck s _ j)
  have hbase : {v ∈ zeroLocus K (RingHom.ker (graphChartMap Y k)) | F.map (eval v) = 0}.Finite := by
    simp only [F, map_weightedGraph_eq_zero_iff idx hidx]
    exact finite_residual_base Y ck k s p hp
  have hsize : mixtureBound h (B+h+1) (Fintype.card (Option (Fin h) ⊕ I)) (d+1) < Fintype.card E :=
    by simpa [Fintype.card_sum] using
      lt_of_le_of_lt (le_max_right _ _ : mixtureBound h (B+h+1) ((h+1)+Fintype.card I) (d+1) ≤
        sliceGridBound h d B (Fintype.card I)) hlo
  obtain ⟨a,ha⟩ := finite_weighted_graph_slice E.subtype Y k hY hh F hFd hFc hbase hsize
  have evalRow (w : Option (Fin h) ⊕ I → K) (j : Fin h) :
      eval w (map E.subtype (graphSliceRow ((algebraMap E₀ E) ∘ c) s p e B (a j))) =
        (F.map (eval w)).eval (E.subtype (a j)) :=
    eval_row_map (E := E) E.subtype _ s p e B (a j) w
  refine ⟨k,E,hE,hhi,hk,s,p,a,?_,?_⟩
  · apply ha.subset
    intro w hw
    exact ⟨hw.1, fun j => (evalRow w j).symm.trans (hw.2 j)⟩
  · obtain ⟨z',hz'⟩ := hp0
    let w := Sum.elim (z' ∘ (_root_.finSuccEquiv h).symm) ck
    have hzero : ∀ j, eval w (residual j) = 0 := by
      intro j
      cases j with
      | inl i => simp [residual, w, fiberResiduals]
      | inr i =>
        simp only [residual, w, fiberResiduals, Sum.elim_inr, eval_sub, eval_X, eval_C,
          Sum.elim_inl, Function.comp_apply, Equiv.symm_apply_apply, sub_eq_zero]
        exact hz'.2 i.val i.property
    refine ⟨_,hz'.1,fun j => ?_⟩
    have h0 := (map_weightedGraph_eq_zero_iff idx hidx residual w).mpr hzero
    exact (evalRow w j).trans (by simp only [F, h0, Polynomial.eval_zero])

end Branch

end BorderVNP
end Computability
end OAI
