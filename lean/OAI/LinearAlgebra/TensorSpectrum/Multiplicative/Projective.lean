import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Ring

/-!
# The projective maps and frozen affine slices in Appendix A.2

These lemmas isolate the actual maps used by the character construction. A
frozen eigenvalue slice is convex; the full nonlinear fixed set is only claimed
to be closed. The last lemma is the compact finite-intersection step, not an
existence theorem for the required finite common fixed points.
-/

noncomputable section

namespace OAI.LinearAlgebra.TensorSpectrum

open Set

variable {S : Type*} [CommMonoidWithZero S]

/-- The normalized multiplication map from Appendix A.2. -/
def projective (z : S) (f : S → ℝ) : S → ℝ :=
  fun x => f (z * x) / f z

/-- Freeze the eigenvalue as a real constant, retaining affine equations. -/
def eigenSlice (z : S) (c : ℝ) : Set (S → ℝ) :=
  {f | ∀ x, f (z * x) = c * f x}

/-- The original nonlinear multiplicativity equations for one multiplier. -/
def multiplicativeSet (z : S) : Set (S → ℝ) :=
  {f | ∀ x, f (z * x) = f z * f x}

theorem projective_one (z : S) (f : S → ℝ) (hz : f z ≠ 0) :
    projective z f 1 = 1 := by
  simp [projective, hz]

theorem projective_zero (z : S) (f : S → ℝ) (hzero : f 0 = 0) :
    projective z f 0 = 0 := by
  simp [projective, hzero]

theorem projective_fixed_iff (z : S) (f : S → ℝ) (hz : f z ≠ 0) :
    projective z f = f ↔ f ∈ multiplicativeSet z := by
  constructor
  · intro h x
    have hx := congrFun h x
    change f (z * x) / f z = f x at hx
    exact (div_eq_iff hz).mp hx |>.trans (mul_comm _ _)
  · intro h
    funext x
    change f (z * x) / f z = f x
    rw [h x, mul_div_cancel_left₀ _ hz]

theorem continuousOn_projective (z : S) (K : Set (S → ℝ))
    (hz : ∀ f ∈ K, f z ≠ 0) : ContinuousOn (projective z) K := by
  apply continuousOn_pi.2
  intro x
  exact (continuous_apply (z * x)).continuousOn.div
    (continuous_apply z).continuousOn hz

theorem eigenSlice_isClosed (z : S) (c : ℝ) : IsClosed (eigenSlice z c) := by
  have h : eigenSlice z c = ⋂ x : S, {f : S → ℝ | f (z * x) = c * f x} := by
    ext f
    simp only [eigenSlice, mem_ofPred_eq, mem_iInter]
  rw [h]
  exact isClosed_iInter fun x =>
    isClosed_eq (continuous_apply (z * x)) (continuous_const.mul (continuous_apply x))

theorem eigenSlice_convex (z : S) (c : ℝ) : Convex ℝ (eigenSlice z c) := by
  intro f hf g hg a b _ _ _ x
  change a * f (z * x) + b * g (z * x) = c * (a * f x + b * g x)
  rw [hf x, hg x]
  ring

theorem multiplicativeSet_isClosed (z : S) : IsClosed (multiplicativeSet z) := by
  have h : multiplicativeSet z =
      ⋂ x : S, {f : S → ℝ | f (z * x) = f z * f x} := by
    ext f
    simp only [multiplicativeSet, mem_ofPred_eq, mem_iInter]
  rw [h]
  exact isClosed_iInter fun x => isClosed_eq (continuous_apply (z * x))
    ((continuous_apply z).mul (continuous_apply x))

/-- All other projective maps preserve every frozen equation. No cancellation
or division by a possibly zero coordinate is needed for this algebraic fact. -/
theorem projective_mem_eigenSlice (z w : S) (c : ℝ) (f : S → ℝ)
    (hf : f ∈ eigenSlice z c) : projective w f ∈ eigenSlice z c := by
  intro x
  change f (w * (z * x)) / f w = c * (f (w * x) / f w)
  rw [show w * (z * x) = z * (w * x) by ac_rfl, hf (w * x)]
  ring

theorem eigenSlice_eigenvalue (z : S) (c : ℝ) (f : S → ℝ)
    (hf : f ∈ eigenSlice z c) (hunit : f 1 = 1) : f z = c := by
  simpa only [mul_one, hunit] using hf 1

theorem eigenSlice_mem_multiplicativeSet (z : S) (c : ℝ) (f : S → ℝ)
    (hf : f ∈ eigenSlice z c) (hunit : f 1 = 1) :
    f ∈ multiplicativeSet z := by
  intro x
  rw [hf x, eigenSlice_eigenvalue z c f hf hunit]

/-- Once a fixed point is obtained, freezing its eigenvalue preserves that
witness and yields a compact convex slice invariant under every projective map. -/
theorem freeze_fixedPoint (K : Set (S → ℝ)) (z : S) (f : S → ℝ)
    (hcompact : IsCompact K) (hconvex : Convex ℝ K) (hf : f ∈ K)
    (hfixed : projective z f = f) (hz : f z ≠ 0)
    (hinvariant : ∀ w, w ≠ 0 → MapsTo (projective w) K K) :
    let L := K ∩ eigenSlice z (f z)
    f ∈ L ∧ IsCompact L ∧ Convex ℝ L ∧
      (∀ w, w ≠ 0 → MapsTo (projective w) L L) := by
  dsimp only
  refine ⟨⟨hf, (projective_fixed_iff z f hz).mp hfixed⟩,
    hcompact.inter_right (eigenSlice_isClosed z (f z)),
    hconvex.inter (eigenSlice_convex z (f z)), ?_⟩
  intro w hw g hg
  exact ⟨hinvariant w hw hg.1, projective_mem_eigenSlice z w (f z) g hg.2⟩

/-- The compactness step in Appendix A.2. Finite common fixed points are an
explicit obligation; this lemma does not assume or assert their existence. -/
theorem multiplicative_of_finite_common_points
    (K : Set (S → ℝ)) (hcompact : IsCompact K)
    (hzero : ∀ f ∈ K, f 0 = 0)
    (hfinite : ∀ F : Finset {z : S // z ≠ 0},
      ∃ f ∈ K, ∀ z ∈ F, f ∈ multiplicativeSet z.val) :
    ∃ f ∈ K, ∀ z x, f (z * x) = f z * f x := by
  have hnonempty : (K ∩ ⋂ z : {z : S // z ≠ 0}, multiplicativeSet z.val).Nonempty := by
    apply hcompact.inter_iInter_nonempty
      (fun z : {z : S // z ≠ 0} => multiplicativeSet z.val)
      (fun z => multiplicativeSet_isClosed z.val)
    intro F
    obtain ⟨f, hf, hF⟩ := hfinite F
    refine ⟨f, hf, ?_⟩
    simp only [mem_iInter]
    exact hF
  obtain ⟨f, hf, hall⟩ := hnonempty
  refine ⟨f, hf, ?_⟩
  intro z x
  by_cases hz : z = 0
  · simp [hz, hzero f hf]
  · exact (mem_iInter.mp hall ⟨z, hz⟩) x

end OAI.LinearAlgebra.TensorSpectrum
