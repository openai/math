import OAI.Computability.VPVNP.Barycenter
import Mathlib.Analysis.Real.Sqrt

/-!
# Four-point inequalities for Grassmannian distance arrays

The proof of Lemma 5.3 uses the squared quadrilateral inequality and its
equality case even for limits of scaled configurations in different CAT(0)
spaces. The midpoint comparison yields a closed system of inequalities on
the array alone. A nonnegative square in the quadrilateral deficit gives the
equality case directly for every array in this closed set.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

open VPVNP.SpectralGeometry

variable {V : Type*}

/-- The squared-distance upper bound from the midpoint of `ac` to `b`. -/
noncomputable def midpointUpper (D : V → V → ℝ) (a b c : V) : ℝ :=
  (D a b + D b c) / 2 - D a c / 4

/-- Closed four-point conditions inherited from CAT(0) squared distances. -/
def catZeroArrays (V : Type*) : Set (V → V → ℝ) :=
  {D | (∀ a b, 0 ≤ D a b) ∧ (∀ a b, D a b = D b a) ∧ (∀ a, D a a = 0) ∧
    (∀ a b c, 0 ≤ midpointUpper D a b c) ∧
    (∀ a b c d, √(D b d) ≤ √(midpointUpper D a b c) + √(midpointUpper D a d c))}

theorem isClosed_catZeroArrays (V : Type*) : IsClosed (catZeroArrays V) := by
  simp only [catZeroArrays, Set.ofPred_and, Set.ofPred_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)))
  · exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_le continuous_const
      ((continuous_apply b).comp (continuous_apply a))
  · exact isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq ((continuous_apply b).comp (continuous_apply a))
        ((continuous_apply a).comp (continuous_apply b))
  · exact isClosed_iInter fun a =>
      isClosed_eq ((continuous_apply a).comp (continuous_apply a)) continuous_const
  · refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun c =>
      isClosed_le continuous_const ?_
    unfold midpointUpper
    fun_prop
  · refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun c =>
      isClosed_iInter fun d => isClosed_le ?_ ?_
    · fun_prop
    · unfold midpointUpper
      fun_prop

/-- Scaling squared distances by any nonnegative factor preserves the closed
four-point conditions. Only the midpoint case of the segment inequality is needed. -/
theorem scaledDistSq_mem_catZeroArrays {X : Type*} [PseudoMetricSpace X]
    (h : HasCATZeroSegments X) (x : V → X) {s : ℝ} (hs : 0 ≤ s) :
    (fun i j => s * dist (x i) (x j) ^ 2) ∈ catZeroArrays V := by
  let D (i j : V) := s * dist (x i) (x j) ^ 2
  have hmid (a c : V) : ∃ w : X, ∀ b : V,
      (√s * dist (x b) w) ^ 2 ≤ midpointUpper D a b c := by
    obtain ⟨w, hw⟩ := h (x a) (x c) (1 / 2) (by norm_num) (by norm_num)
    refine ⟨w, fun b => ?_⟩
    have hb := hw (x b)
    rw [dist_comm (x b) (x a)] at hb
    rw [mul_pow, Real.sq_sqrt hs]
    unfold midpointUpper D
    linarith only [mul_le_mul_of_nonneg_left hb hs]
  refine ⟨fun i j => mul_nonneg hs (sq_nonneg _), fun i j => ?_, fun i => by simp, ?_, ?_⟩
  · dsimp
    rw [dist_comm]
  · intro a b c
    obtain ⟨w, hw⟩ := hmid a c
    exact (sq_nonneg _).trans (hw b)
  · intro a b c d
    obtain ⟨w, hw⟩ := hmid a c
    rw [Real.sqrt_mul hs, Real.sqrt_sq dist_nonneg]
    calc
      √s * dist (x b) (x d) ≤ √s * (dist (x b) w + dist (x d) w) := by
        rw [dist_comm (x d) w]
        exact mul_le_mul_of_nonneg_left (dist_triangle _ _ _) (Real.sqrt_nonneg _)
      _ = √s * dist (x b) w + √s * dist (x d) w := mul_add _ _ _
      _ ≤ _ := add_le_add (Real.le_sqrt_of_sq_le (hw b)) (Real.le_sqrt_of_sq_le (hw d))

/-- The four-point properties used by the averaging and rigidity arguments
on the binary Grassmannian. At equality both pairs of opposite sides agree. -/
structure QuadBounds (D : V → V → ℝ) : Prop where
  nonneg : ∀ a b, 0 ≤ D a b
  symm : ∀ a b, D a b = D b a
  diag : ∀ a, D a a = 0
  quad : ∀ a b c d, D a c + D b d ≤ D a b + D b c + D c d + D d a
  opposite : ∀ a b c d, D a c + D b d = D a b + D b c + D c d + D d a →
    D a b = D c d ∧ D b c = D d a

theorem quadBounds_of_mem_catZeroArrays {D : V → V → ℝ} (h : D ∈ catZeroArrays V) :
    QuadBounds D := by
  obtain ⟨hn, hs, hd, hm, ht⟩ := h
  have hdefect (a b c d : V) :
      D a c + D b d + (√(midpointUpper D a b c) - √(midpointUpper D a d c)) ^ 2 ≤
        D a b + D b c + D c d + D d a := by
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _)
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr (ht a b c d)
    rw [Real.sq_sqrt (hn b d)] at hsq
    have hbound : D b d + (√(midpointUpper D a b c) - √(midpointUpper D a d c)) ^ 2 ≤
        2 * midpointUpper D a b c + 2 * midpointUpper D a d c := by
      nlinarith only [hsq, Real.sq_sqrt (hm a b c), Real.sq_sqrt (hm a d c)]
    unfold midpointUpper at *
    linarith only [hbound, hs d c, hs a d]
  have hsum (a b c d : V)
      (he : D a c + D b d = D a b + D b c + D c d + D d a) :
      D a b + D b c = D c d + D d a := by
    have hz : (√(midpointUpper D a b c) - √(midpointUpper D a d c)) ^ 2 = 0 :=
      le_antisymm (by linarith only [he, hdefect a b c d]) (sq_nonneg _)
    have heq : √(midpointUpper D a b c) = √(midpointUpper D a d c) :=
      sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
    have heq' := (Real.sqrt_inj (hm a b c) (hm a d c)).mp heq
    unfold midpointUpper at heq'
    linarith only [heq', hs d c, hs a d]
  refine ⟨hn, hs, hd, fun a b c d => ?_, fun a b c d he => ?_⟩
  · linarith only [hdefect a b c d, sq_nonneg (√(midpointUpper D a b c) -
      √(midpointUpper D a d c))]
  · have h₁ := hsum a b c d he
    have h₂ := hsum b c d a (by linarith only [he, hs c a])
    constructor <;> linarith only [h₁, h₂]

end Grassmann

end VPVNP
end Computability
end OAI
