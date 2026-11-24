import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Geometry.Convex.Cone.Pointed

/-! # Extreme positive states in spectral comparison

In Appendix A.1 the localization has an order unit. Its rational-linear
positive functionals normalized at the unit form a compact subset of the
space of real-valued functions, with the topology of pointwise convergence.
An extreme such functional is multiplicative on the tensor generators.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Spectral

open Set

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- Real-valued rational-linear functionals normalized to one at the unit and nonnegative on
the specified cone. -/
def states (P : PointedCone ℚ A) : Set (A → ℝ) :=
  {f | f 1 = 1 ∧ (∀ x y, f (x + y) = f x + f y) ∧
    (∀ (r : ℚ) x, f (r • x) = r • f x) ∧ ∀ x ∈ P, 0 ≤ f x}

/-- The rational-linear map underlying a normalized positive state on the cone. -/
def stateLinearMap {P : PointedCone ℚ A} {f : A → ℝ} (hf : f ∈ states P) : A →ₗ[ℚ] ℝ where
  toFun := f
  map_add' := hf.2.1
  map_smul' := hf.2.2.1

theorem states_isClosed (P : PointedCone ℚ A) : IsClosed (states P) := by
  unfold states
  simp only [ofPred_and, ofPred_forall]
  refine (isClosed_eq (continuous_apply 1) continuous_const).inter ?_
  refine (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq
    (continuous_apply (x + y)) (by fun_prop)).inter ?_
  refine (isClosed_iInter fun (r : ℚ) => isClosed_iInter fun (x : A) =>
    isClosed_eq (continuous_apply (r • x)) (by fun_prop)).inter ?_
  exact isClosed_iInter fun (x : A) => isClosed_iInter fun (_ : x ∈ P) =>
    isClosed_le continuous_const (continuous_apply x)

theorem states_isCompact (P : PointedCone ℚ A)
    (orderUnit : ∀ x : A, ∃ n : ℕ, n • (1 : A) + x ∈ P) : IsCompact (states P) := by
  choose bound hb using orderUnit
  refine (isCompact_univ_pi fun (x : A) =>
    isCompact_Icc (a := -(bound x : ℝ)) (b := (bound (-x) : ℝ))).of_isClosed_subset
    (states_isClosed P) ?_
  intro f hf x _
  let L := stateLinearMap hf
  have h1 : L 1 = 1 := hf.1
  have hpos (a : A) : 0 ≤ L (bound a • (1 : A) + a) := hf.2.2.2 _ (hb a)
  have hlo := hpos x
  have hhi := hpos (-x)
  simp only [map_add, map_neg] at hlo hhi
  rw [map_nsmul L, h1, nsmul_eq_mul, mul_one] at hlo hhi
  change -(bound x : ℝ) ≤ L x ∧ L x ≤ bound (-x)
  constructor <;> linarith

/-- A minimizing face contains a state extreme in the original set. -/
theorem exists_extreme_state_le (P : PointedCone ℚ A)
    (orderUnit : ∀ x : A, ∃ n : ℕ, n • (1 : A) + x ∈ P)
    (z : A) {f₀ : A → ℝ} (hf₀ : f₀ ∈ states P) :
    ∃ f ∈ (states P).extremePoints ℝ, f z ≤ f₀ z := by
  let s := states P
  let face := {f ∈ s | ∀ g ∈ s, -g z ≤ -f z}
  have exposed : IsExposed ℝ s face := fun _ => ⟨-ContinuousLinearMap.proj z, rfl⟩
  have comp := states_isCompact P orderUnit
  obtain ⟨g, hg, hmax⟩ := comp.exists_isMaxOn ⟨f₀, hf₀⟩ (continuous_apply z).neg.continuousOn
  obtain ⟨f, h⟩ := (exposed.isCompact comp).extremePoints_nonempty ⟨g, hg, hmax⟩
  exact ⟨f, exposed.isExtreme.extremePoints_subset_extremePoints h,
    neg_le_neg_iff.mp (h.1.2 _ hf₀)⟩

private theorem reweighted_state {P : PointedCone ℚ A} {f : A → ℝ} (hf : f ∈ states P)
    (u : A) (hu : 0 < f u) (hstable : ∀ x ∈ P, u * x ∈ P) :
    (fun x => f (u * x) / f u) ∈ states P := by
  refine ⟨by simp [hu.ne'], fun x y => ?_, fun r x => ?_, fun x hx => ?_⟩
  · dsimp only
    rw [mul_add, hf.2.1, add_div]
  · dsimp only
    rw [mul_smul_comm, hf.2.2.1]
    simp [Rat.smul_def, mul_div_assoc]
  · exact div_nonneg (hf.2.2.2 _ (hstable x hx)) hu.le

/-- Splitting the unit into two positive multipliers makes both reweighted
states coincide with an extreme state. This is the multiplicativity step of A.1. -/
theorem extreme_state_mul_of_split {P : PointedCone ℚ A} {f : A → ℝ}
    (he : f ∈ (states P).extremePoints ℝ) {u v : A} (huv : u + v = 1)
    (hu : 0 < f u) (hv : 0 < f v)
    (su : ∀ x ∈ P, u * x ∈ P) (sv : ∀ x ∈ P, v * x ∈ P) :
    (∀ x, f (u*x) = f u * f x) ∧ ∀ x, f (v*x) = f v * f x := by
  let g := fun x => f (u*x) / f u
  let h := fun x => f (v*x) / f v
  have hf := he.1
  have hg : g ∈ states P := reweighted_state hf u hu su
  have hh : h ∈ states P := reweighted_state hf v hv sv
  have hseg : f ∈ openSegment ℝ g h := by
    refine ⟨f u, f v, hu, hv, by rw [← hf.2.1, huv, hf.1], ?_⟩
    funext x
    change f u * (f (u*x) / f u) + f v * (f (v*x) / f v) = f x
    rw [mul_div_cancel₀ _ hu.ne', mul_div_cancel₀ _ hv.ne', ← hf.2.1, ← add_mul, huv, one_mul]
  have fg := (mem_extremePoints_iff_left.mp he).2 _ hg _ hh hseg
  have fh := (mem_extremePoints_iff_left.mp he).2 _ hh _ hg ((openSegment_symm ℝ g h) ▸ hseg)
  constructor
  · intro x
    have hx : f (u*x) / f u = f x := congrFun fg x
    exact (div_eq_iff hu.ne').mp hx |>.trans (mul_comm _ _)
  · intro x
    have hx : f (v*x) / f v = f x := congrFun fh x
    exact (div_eq_iff hv.ne').mp hx |>.trans (mul_comm _ _)

/-- If `v*s=u`, the split proves multiplicativity on the original element `s`. -/
theorem extreme_state_mul_generator {P : PointedCone ℚ A} {f : A → ℝ}
    (he : f ∈ (states P).extremePoints ℝ) {s u v : A} (huv : u+v=1) (hs : v*s=u)
    (hu : 0 < f u) (hv : 0 < f v)
    (su : ∀ x ∈ P, u*x ∈ P) (sv : ∀ x ∈ P, v*x ∈ P) (x : A) :
    f (s*x) = f s * f x := by
  obtain ⟨hmulu, hmulv⟩ := extreme_state_mul_of_split he huv hu hv su sv
  apply mul_left_cancel₀ hv.ne'
  rw [← hmulv, ← mul_assoc v s x, hs, hmulu, ← mul_assoc, ← hmulv, hs]

end Spectral

end VPVNP
end Computability
end OAI
