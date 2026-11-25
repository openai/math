import Mathlib.LinearAlgebra.Matrix.BilinearForm
import OAI.Computability.NearSquareRoot.InterchangeFar

/-! # Rational address coordinates for the label routing

Two constant coordinates and one coordinate for each outer position and inner
word suffice to realize the Gram blocks used by the interchange. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

abbrev GramIndex (h : ℕ) (U : Type*) := Bool ⊕ (Fin h × U)

/-- The ambient space has dimension independent of the number of outer labels. -/
theorem card_gramIndex (h : ℕ) (U : Type*) [Fintype U] :
    Fintype.card (GramIndex h U) = 2 + h * Fintype.card U := by simp [GramIndex]

private def orientation : Bool → ℚ
  | false => 1
  | true => -1

variable {h : ℕ} {U : Type*} [Fintype U] [DecidableEq U]

/-- A rational coordinate form. The two special basis vectors are orthonormal;
distinct outer positions are mutually orthogonal. -/
def gramCoefficients (weights : U → U → ℚ) (p : ℕ) :
    Matrix (GramIndex h U) (GramIndex h U) ℚ
  | .inl b, .inl c => if b = c then 1 else 0
  | .inr (i,u), .inr (j,v) => if i = j then -weights u v / p else 0
  | _, _ => 0

omit [Fintype U] [DecidableEq U] in
theorem gramCoefficients_symm (weights : U → U → ℚ)
    (hs : ∀ u v, weights u v = weights v u) (p : ℕ) :
    (gramCoefficients (h := h) weights p).IsSymm := by
  apply Matrix.IsSymm.ext
  rintro (b | ⟨i,u⟩) (c | ⟨j,v⟩) <;>
    simp only [gramCoefficients]
  · simp [eq_comm]
  · simp [eq_comm, hs]

/-- The two vectors at a label share the inner-word coordinates with opposite signs. -/
def gramVector (b : Bool) (v : Fin h → U) : GramIndex h U → ℚ :=
  Pi.single (.inl b) 1 +
    orientation b • ∑ i : Fin h, Pi.single (.inr (i, v i)) 1

theorem gramVector_pairing (weights : U → U → ℚ) (p : ℕ)
    (v w : Fin h → U) (b c : Bool) :
    (gramCoefficients weights p).toBilin' (gramVector b v) (gramVector c w) =
      if b = c then 1 - (∑ i, weights (v i) (w i)) / p
      else (∑ i, weights (v i) (w i)) / p := by
  classical
  simp only [gramVector, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    map_sum, LinearMap.sum_apply, Matrix.toBilin'_single]
  simp [gramCoefficients, div_eq_mul_inv, Finset.sum_neg_distrib]
  cases b <;> cases c <;> simp [orientation, sub_eq_add_neg, ← Finset.sum_mul]

/-- Insert the two main coordinates, switching their order on destination endpoints. -/
def gramEmbed (side : Bool) (v : Fin h → U) :
    (Bool → ℚ) →ₗ[ℚ] (GramIndex h U → ℚ) :=
  Fintype.linearCombination ℚ fun b => gramVector (side.xor b) v

/-- Read the coordinates by pairing against the oriented vectors at this endpoint. -/
noncomputable def gramRead (weights : U → U → ℚ) (p : ℕ) (side : Bool) (v : Fin h → U) :
    (GramIndex h U → ℚ) →ₗ[ℚ] (Bool → ℚ) :=
  LinearMap.pi fun b => (gramCoefficients weights p).toBilin' (gramVector (side.xor b) v)

/-- Within a side the count is zero and across sides it is exactly `p`. The
orientation reversal consequently gives identity transfers between *all*
pairs of endpoints in a rectangle. -/
theorem gramRead_comp_embed (weights : U → U → ℚ) {p : ℕ} (hp : 0 < p)
    (s t : Bool) (v w : Fin h → U)
    (hc : (∑ i, weights (v i) (w i)) = if s = t then 0 else (p : ℚ)) :
    (gramRead weights p s v).comp (gramEmbed t w) = LinearMap.id := by
  have hpair (b c : Bool) :
      (gramCoefficients weights p).toBilin' (gramVector (s.xor b) v) (gramVector (t.xor c) w)
        = if b = c then 1 else 0 := by
    rw [gramVector_pairing, hc]
    have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
    cases s <;> cases t <;> cases b <;> cases c <;> simp [hp']
  apply LinearMap.ext
  intro x
  funext b
  simp only [LinearMap.comp_apply, gramRead, LinearMap.pi_apply, gramEmbed,
    Fintype.linearCombination_apply, map_sum, map_smul, hpair, LinearMap.id_apply]
  simp [mul_ite]

/-- The Boolean far relation in the rectangle partition supplies the Gram
hypothesis directly as a count of outer coordinates. -/
theorem gramRead_comp_embed_farCount (far : U → U → Prop) [DecidableRel far]
    {p : ℕ} (hp : 0 < p) (s t : Bool) (v w : Fin h → U)
    (hc : (Finset.univ.filter fun i => far (v i) (w i)).card =
      if s = t then 0 else p) :
    (gramRead (fun u u' => if far u u' then 1 else 0) p s v).comp (gramEmbed t w) =
      LinearMap.id := by
  apply gramRead_comp_embed _ hp
  simpa only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    using congrArg (fun n : ℕ => (n : ℚ)) hc

/-- For an irreflexive far relation each label embeds its two-dimensional
coordinate space, so the active columns can be completed to a basis. -/
theorem gramEmbed_injective (far : U → U → Prop) [DecidableRel far]
    (hir : ∀ a, ¬ far a a) {p : ℕ} (hp : 0 < p) (s : Bool) (v : Fin h → U) :
    Function.Injective (gramEmbed s v) := by
  have hcomp := gramRead_comp_embed_farCount far hp s s v v (by simp [hir])
  have hleft : Function.LeftInverse
      (gramRead (fun u u' => if far u u' then 1 else 0) p s v) (gramEmbed s v) :=
    fun x => LinearMap.congr_fun hcomp x
  exact hleft.injective

/-- Identity transfer for the actual Hamming rectangles on binary-string letters. -/
theorem gramRead_comp_embed_rectangle {h p k : ℕ} (hp : 0 < p)
    {r : FarRectangles.LabelKey h p k hp} {s t : Bool} {v w : FarRectangles.Label h k}
    (hv : FarRectangles.LabelIncident s r v) (hw : FarRectangles.LabelIncident t r w) :
    (gramRead (fun u u' => if hammingDist u u' = p then 1 else 0) p s v).comp
      (gramEmbed t w) = LinearMap.id := by
  apply gramRead_comp_embed_farCount (fun u u' => hammingDist u u' = p) hp
  cases s <;> cases t
  · exact FarRectangles.count_far_same_side hv hw
  · exact FarRectangles.count_far_across hv hw
  · simpa only [hammingDist_comm, Bool.true_eq_false, ite_false] using
      FarRectangles.count_far_across hw hv
  · exact FarRectangles.count_far_same_side hv hw

end Interchange

end NearSquareRoot
end Computability
end OAI
