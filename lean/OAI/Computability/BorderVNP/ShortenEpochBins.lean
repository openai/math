import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Group.Action
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Tactic

/-!
# Finite bins for moving and matching

A compact set of positions and directions admits arbitrarily fine finite
bins with null boundaries. Taking all finite-group translates of the
membership tests makes the bins equivariant, including at boundary ties.
The expected counts for any invariant ideal law are consequently constant
along the permuted bin addresses used in Lemma 6.1.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open Metric MeasureTheory Set

variable {G X : Type*} [Group G] [Fintype G] [PseudoMetricSpace X] [MeasurableSpace X]
  [BorelSpace X] [MulAction G X] [ContinuousConstSMul G X]

/-- A finite bin code carrying the action on the addresses of directions. -/
structure DirectionBins (G X : Type*) [Group G] [MulAction G X] where
  /-- Type of addresses, including empty bins. -/
  Address : Type
  finiteAddress : Fintype Address
  /-- Public address of a point, with a single outcome even on seams. -/
  code : X → Address
  /-- Action of a signed factor permutation on bin addresses. -/
  perm : G → Equiv.Perm Address
  equivariant : ∀ g x, code (g • x) = perm g (code x)

attribute [instance] DirectionBins.finiteAddress

private theorem null_frontier_finInter {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    (μ : Measure Y) {κ : Type*} (s : Finset κ) (A : κ → Set Y)
    (h : ∀ i ∈ s, μ (frontier (A i)) = 0) :
    μ (frontier (⋂ i ∈ s, A i)) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.set_biInter_insert]
    exact null_frontier_inter (h _ (Finset.mem_insert_self _ _))
      (ih (fun j hj => h _ (Finset.mem_insert_of_mem hj)))

/-- Arbitrarily small measurable bins with null boundary, permuted exactly by
the finite group. Compactness is needed only on the set of configurations
that can occur, which permits using a closed lifted tile in the full host. -/
theorem exists_directionBins (μ : Measure X) [SFinite μ] [SMulInvariantMeasure G X μ]
    {S : Set X} (hS : IsCompact S) {δ : ℝ} (hδ : 0 < δ) :
    ∃ bins : DirectionBins G X,
      (∀ a, MeasurableSet (bins.code ⁻¹' {a}) ∧ μ (frontier (bins.code ⁻¹' {a})) = 0) ∧
      ∀ x ∈ S, ∀ y, bins.code x = bins.code y → dist x y < δ := by
  classical
  have radius (x : X) : ∃ r ∈ Ioo (0 : ℝ) (δ / 2), μ (frontier (ball x r)) = 0 := by
    simpa using exists_null_frontier_thickening μ {x} (show 0 < δ/2 by positivity)
  choose r hr hnull using radius
  obtain ⟨s, hcover⟩ := hS.elim_finite_subcover (fun x => ball x (r x))
    (fun _ => isOpen_ball) (fun x _ => mem_iUnion.mpr ⟨x, mem_ball_self (hr x).1⟩)
  let n := s.card
  let centers : Fin n → X := fun i => ((Fintype.equivFin s).symm (Fin.cast (by simp [n]) i)).val
  have hc (x : X) (hx : x ∈ S) : ∃ i, x ∈ ball (centers i) (r (centers i)) := by
    obtain ⟨c, hcs, hxc⟩ := mem_iUnion₂.mp (hcover hx)
    let i := (Fintype.equivFin s) ⟨c, hcs⟩
    exact ⟨Fin.cast (by simp [n]) i, by simpa [centers, i] using hxc⟩
  let code (x : X) : (Fin (Fintype.card G) × Fin n → Bool) := fun ji =>
    decide ((Fintype.equivFin G).symm ji.1 • x ∈ ball (centers ji.2) (r (centers ji.2)))
  let right (g : G) := (Fintype.equivFin G).symm.trans ((Equiv.mulRight g).trans (Fintype.equivFin G))
  let perm (g : G) : Equiv.Perm (Fin (Fintype.card G) × Fin n → Bool) :=
    ((right g).prodCongr (Equiv.refl (Fin n))).symm.arrowCongr (Equiv.refl Bool)
  let bins : DirectionBins G X := {
    Address := Fin (Fintype.card G) × Fin n → Bool
    finiteAddress := inferInstance
    code := code
    perm := perm
    equivariant := by
      intro g x
      funext ji
      simp [code, perm, right, mul_smul] }
  refine ⟨bins, ?_, ?_⟩
  · intro a
    let test (ji : Fin (Fintype.card G) × Fin n) : Set X :=
      (((Fintype.equivFin G).symm ji.1 • ·) : X → X) ⁻¹' ball (centers ji.2) (r (centers ji.2))
    let atom (ji : Fin (Fintype.card G) × Fin n) := if a ji then test ji else (test ji)ᶜ
    have hset : bins.code ⁻¹' {a} = ⋂ ji, atom ji := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_iInter]
      change code x = a ↔ ∀ ji, x ∈ atom ji
      rw [funext_iff]
      apply forall_congr'
      intro ji
      cases hj : a ji <;> simp [atom, test, code, hj]
    rw [hset]
    have htest (ji : Fin (Fintype.card G) × Fin n) : MeasurableSet (test ji) :=
      measurableSet_ball.preimage (continuous_const_smul _).measurable
    have hatom (ji : Fin (Fintype.card G) × Fin n) : μ (frontier (atom ji)) = 0 := by
      have hpre : μ (frontier (test ji)) = 0 :=
        measure_mono_null ((continuous_const_smul _).frontier_preimage_subset _)
          (measure_preimage_smul_null (hnull (centers ji.2)) _)
      cases hj : a ji <;> simp [atom, hj, hpre, frontier_compl]
    constructor
    · exact MeasurableSet.iInter fun ji => by cases hj : a ji <;> simp [atom, hj, htest]
    · simpa using null_frontier_finInter μ Finset.univ atom (fun i _ => hatom i)
  · intro x hx y he
    obtain ⟨i, hi⟩ := hc x hx
    have he' := congrFun he ((Fintype.equivFin G) 1, i)
    change code x _ = code y _ at he'
    simp only [code, Equiv.symm_apply_apply, one_smul, decide_eq_decide] at he'
    have hy := he'.mp hi
    change dist x (centers i) < r (centers i) at hi
    change dist y (centers i) < r (centers i) at hy
    calc
      _ ≤ dist x (centers i) + dist (centers i) y := dist_triangle _ _ _
      _ < δ := by rw [dist_comm (centers i) y]; linarith only [hi, hy, (hr (centers i)).2]

omit [Fintype G] [PseudoMetricSpace X] [BorelSpace X] [ContinuousConstSMul G X] in
/-- Invariant ideal law gives invariant bin counts, even if different bins
have different sizes. -/
theorem DirectionBins.ideal_mass (bins : DirectionBins G X) (μ : Measure X)
    [SMulInvariantMeasure G X μ] (g : G) (b : bins.Address) :
    μ (bins.code ⁻¹' {bins.perm g b}) = μ (bins.code ⁻¹' {b}) := by
  rw [← measure_preimage_smul μ g]
  congr 1
  ext x
  change bins.code (g • x) = bins.perm g b ↔ bins.code x = b
  rw [bins.equivariant, Equiv.apply_eq_iff_eq]

end Epoch

end BorderVNP
end Computability
end OAI
