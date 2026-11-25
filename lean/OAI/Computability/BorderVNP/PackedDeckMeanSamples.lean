import OAI.Computability.BorderVNP.PackedDeckMeanMath
import OAI.Computability.BorderVNP.CoverPackBins

/-! # Clearing the actual finite Hecke candidate law

The motion-word tuple and permutation have a rational distribution fixed
before the deck depth. A full pack sample adds an independently uniform
deck translation. Integerizing the nondeck distribution therefore introduces
only one depth-independent denominator in addition to the product deck order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedDeckMean

open BorderVNP.Cover BorderVNP.Hecke
open scoped Classical

variable {G I : Type*} [Group G] (Γ : Subgroup G) (z : G)
variable [Fintype (Cosets (intersection Γ z))] [Fintype I]

/-- The finite pack candidate before any deck translation is chosen. -/
abbrev MotionCandidate (I : Type*) (n : ℕ) := Equiv.Perm I × ProductSample Γ z I n

/-- Exact probability of the candidate's uniform permutation and independently
sampled Hecke words. -/
noncomputable def motionProbability {n : ℕ} (c : MotionCandidate Γ z I n) : ℚ :=
  productWeight Γ z n c.2 / Fintype.card (Equiv.Perm I)

/-- Every actual permutation and word tuple has positive rational probability. -/
theorem motionProbability_pos {n : ℕ} (c : MotionCandidate Γ z I n) : 0 < motionProbability Γ z c :=
  div_pos (productWeight_pos Γ z n _) (by positivity)

/-- The nondeck candidate weights alone sum to one. -/
theorem sum_motionProbability (n : ℕ) :
    ∑ c : MotionCandidate Γ z I n, motionProbability Γ z c = 1 := by
  simp only [motionProbability,Fintype.sum_prod_type,← Finset.sum_div,sum_productWeight,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hp : (Fintype.card (Equiv.Perm I) : ℚ) ≠ 0 := by positivity
  field_simp

/-- The pack law is the product of the finite nondeck probability and the
uniform probability of the specified product deck translation. -/
theorem packWeight_factor {d n : ℕ} (s : PackSample Γ z I d n) :
    packWeight Γ z s = motionProbability Γ z (s.1,s.2.1) / Fintype.card (I → Deck d) := by
  simp only [packWeight,motionProbability,div_eq_mul_inv,mul_inv_rev]
  ring

/-- The actual uniform posttranslation moves old tile `h⁻¹*x` into tile `x`.
Averaging all pack samples gives the exact rational mean used by the scan. -/
theorem pack_mean_eq {B : Type*} {d n : ℕ}
    (counts : MotionCandidate Γ z I n → B → (I → Deck d) → ℕ) (b : B) (x : I → Deck d) :
    (∑ s : PackSample Γ z I d n, packWeight Γ z s *
      (counts (s.1,s.2.1) b (s.2.2⁻¹*x) : ℚ)) =
      mean (motionProbability Γ z) counts b x := by
  simp only [packWeight_factor,mean,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro π _
  apply Finset.sum_congr rfl
  intro w _
  let c : MotionCandidate Γ z I n := (π,w)
  have hi : (∑ h : I → Deck d, (counts c b (h⁻¹*x) : ℚ)) =
      ∑ h : I → Deck d, (counts c b (h*x) : ℚ) :=
    Equiv.sum_comp (Equiv.inv _) (fun h => (counts c b (h*x) : ℚ))
  change (∑ h : I → Deck d, (motionProbability Γ z c / _) * (counts c b (h⁻¹*x) : ℚ)) = _
  rw [← Finset.mul_sum,hi]
  ring

/-- The actual pack expectation after enumerating the finite nondeck catalog
by physical row indices. -/
theorem indexed_pack_mean_eq {B : Type*} {d n m : ℕ}
    (index : Fin m ≃ MotionCandidate Γ z I n)
    (counts : Fin m → B → (I → Deck d) → ℕ) (b : B) (x : I → Deck d) :
    (∑ s : PackSample Γ z I d n, packWeight Γ z s *
      (counts (index.symm (s.1,s.2.1)) b (s.2.2⁻¹*x) : ℚ)) =
      mean (fun j => motionProbability Γ z (index j)) counts b x := by
  rw [pack_mean_eq Γ z (fun c => counts (index.symm c))]
  unfold mean
  simpa only [index.symm_apply_apply] using (Equiv.sum_comp index (fun c =>
    motionProbability Γ z c * ((∑ h, (counts (index.symm c) b (h*x) : ℚ)) / Fintype.card (I → Deck d)))).symm

/-- Reindex the quaternion pack candidates by the finite array used by the
Boolean circuit. The same natural numerators and denominator work at every
depth, including in the full pack probability. -/
theorem quaternion_candidate_numerators {n m : ℕ}
    (index : Fin m ≃ MotionCandidate (Cover.Frame.lattice 1) Cover.Frame.elliptic I n) :
    ∃ (P : ℕ) (pnum : Fin m → ℕ), 0 < P ∧ ∑ j, pnum j = P ∧
      (∀ j, pnum j ≤ P) ∧
      (∀ j, motionProbability (Cover.Frame.lattice 1) Cover.Frame.elliptic (index j) = (pnum j : ℚ)/P) ∧
      ∀ (d : ℕ) (j : Fin m) (h : I → Deck d),
        packWeight (Cover.Frame.lattice 1) Cover.Frame.elliptic ((index j).1,(index j).2,h) =
          (pnum j : ℚ) / (P * Fintype.card (I → Deck d) : ℕ) := by
  let prob (j : Fin m) := motionProbability (Cover.Frame.lattice 1) Cover.Frame.elliptic (index j)
  have hs : ∑ j, prob j = 1 :=
    (Equiv.sum_comp index _).trans (sum_motionProbability (Cover.Frame.lattice 1) Cover.Frame.elliptic n)
  obtain ⟨P,pnum,hP,hS,he,hbound⟩ := common_probability_denominator prob
    (fun j => (motionProbability_pos _ _ (index j)).le) hs
  refine ⟨P,pnum,hP,hS,hbound,he,?_⟩
  intro d j h
  rw [packWeight_factor]
  change prob j / _ = _
  rw [he,Nat.cast_mul,div_div]

end PackedDeckMean

end BorderVNP
end Computability
end OAI
