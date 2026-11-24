import OAI.Computability.VPVNP.SpectralLocalizationCone
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# Compactness margins for spectral comparison and exact extension

Appendix A.1 turns a pointwise strict comparison into a single integer
margin. In the proof of Theorem 2.4, failure to match every prescribed
generator yields a finite set of generators and a single multiplicative
margin, in one of the two ratio directions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Spectral

open Set

/-- Monotone semiring homomorphisms, viewed in the ambient space of
real-valued functions on the restriction semiring. -/
def spectrumValues (S : Type*) [CommSemiring S] [Preorder S] : Set (S → ℝ) :=
  {g | ∃ F : S →+* ℝ, Monotone F ∧ ⇑F = g}

theorem spectrumValues_isClosed (S : Type*) [CommSemiring S] [Preorder S] :
    IsClosed (spectrumValues S) := by
  have heq : spectrumValues S = {g : S → ℝ | g 0 = 0 ∧ g 1 = 1 ∧
      (∀ x y, g (x+y) = g x + g y) ∧ (∀ x y, g (x*y) = g x * g y) ∧
      (∀ x y, x ≤ y → g x ≤ g y)} := by
    ext g
    constructor
    · rintro ⟨F, hF, rfl⟩
      exact ⟨F.map_zero, F.map_one, F.map_add, F.map_mul, fun _ _ h => hF h⟩
    · rintro ⟨h₀, h₁, hAdd, hMul, hOrder⟩
      let F : S →+* ℝ :=
        { toFun := g
          map_zero' := h₀
          map_one' := h₁
          map_add' := hAdd
          map_mul' := hMul }
      exact ⟨F, fun _ _ h => hOrder _ _ h, rfl⟩
  rw [heq]
  simp only [ofPred_and, ofPred_forall]
  exact (isClosed_eq (continuous_apply 0) continuous_const).inter <|
    (isClosed_eq (continuous_apply 1) continuous_const).inter <|
    (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq
      (continuous_apply (x+y)) ((continuous_apply x).add (continuous_apply y))).inter <|
    (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq
      (continuous_apply (x*y)) ((continuous_apply x).mul (continuous_apply y))).inter <|
    isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun (_ : x ≤ y) =>
      isClosed_le (continuous_apply x) (continuous_apply y)

/-- Tychonoff compactness for the spectral points of Section 2. Each tensor
coordinate lies between zero and an integer rank bound. -/
theorem spectrumValues_isCompact {S : Type*} [CommSemiring S] [Preorder S]
    (H : OrderBounds S) : IsCompact (spectrumValues S) := by
  choose bound hb using H.bounded
  refine (isCompact_univ_pi fun x : S => isCompact_Icc (a := (0 : ℝ)) (b := bound x)).of_isClosed_subset
    (spectrumValues_isClosed S) ?_
  rintro _ ⟨F, hF, rfl⟩ x _
  exact ⟨by simpa using hF (H.zero_le x), by simpa using hF (hb x)⟩

/-- A uniform integer margin for strict comparison over a compact spectrum,
with the topology of pointwise convergence. -/
theorem compact_strict_comparison_margin {S : Type*} {K : Set (S → ℝ)}
    (hK : IsCompact K) {X Y : S} (h : ∀ F ∈ K, F X < F Y) :
    ∃ b : ℕ, ∀ F ∈ K, ((b : ℝ) + 1) * F X < (b : ℝ) * F Y := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, by simp⟩
  let r (F : S → ℝ) := F X / (F Y - F X)
  have hc : ContinuousOn r K := (continuous_apply X).continuousOn.div
    ((continuous_apply Y).sub (continuous_apply X)).continuousOn
    (fun F hF => (sub_pos.mpr (h F hF)).ne')
  obtain ⟨G, _, hG⟩ := hK.exists_isMaxOn hne hc
  obtain ⟨b, hb⟩ := exists_nat_gt (r G)
  refine ⟨b, fun F hF => ?_⟩
  have hlt : r F < b := (hG hF).trans_lt hb
  have hb' := (div_lt_iff₀ (sub_pos.mpr (h F hF))).mp hlt
  linarith

/-- A finite set of generators detects every failure to match the target
values with a uniform relative gap. It can include any specified generators. -/
theorem compact_finite_generator_gap {ι Ω : Type*} [TopologicalSpace Ω] {K : Set Ω}
    (hK : IsCompact K) (value : ι → Ω → ℝ) (target : ι → ℝ)
    (hc : ∀ i, Continuous (value i)) (ht : ∀ i, 0 < target i)
    (hv : ∀ x ∈ K, ∀ i, 0 < value i x)
    (hmismatch : ∀ x ∈ K, ∃ i, value i x ≠ target i)
    (required : Finset ι) :
    ∃ G : Finset ι, required ⊆ G ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ K, ∃ i ∈ G, 1 + δ ≤ value i x / target i ∨ 1 + δ ≤ target i / value i x := by
  classical
  let I := ι × {δ : ℝ // 0 < δ}
  let U (p : I) := {x | (1 + p.2.val) * target p.1 < value p.1 x} ∪
    {x | (1 + p.2.val) * value p.1 x < target p.1}
  have hopen (p : I) : IsOpen (U p) :=
    (isOpen_lt continuous_const (hc p.1)).union
      (isOpen_lt (continuous_const.mul (hc p.1)) continuous_const)
  have hcover : K ⊆ ⋃ p, U p := by
    intro x hx
    obtain ⟨i, hi⟩ := hmismatch x hx
    rcases lt_or_gt_of_ne hi with h | h
    · have hr : 1 < target i / value i x := (one_lt_div (hv x hx i)).mpr h
      obtain ⟨c, hc₁, hc₂⟩ := exists_between hr
      refine mem_iUnion.mpr ⟨(i, ⟨c - 1, sub_pos.mpr hc₁⟩), Or.inr ?_⟩
      change (1 + (c - 1)) * value i x < target i
      simpa using (lt_div_iff₀ (hv x hx i)).mp hc₂
    · have hr : 1 < value i x / target i := (one_lt_div (ht i)).mpr h
      obtain ⟨c, hc₁, hc₂⟩ := exists_between hr
      refine mem_iUnion.mpr ⟨(i, ⟨c - 1, sub_pos.mpr hc₁⟩), Or.inl ?_⟩
      change (1 + (c - 1)) * target i < value i x
      simpa using (lt_div_iff₀ (ht i)).mp hc₂
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hopen hcover
  rcases s.eq_empty_or_nonempty with rfl | hne
  · have : K = ∅ := by simpa using hs
    exact ⟨required, Finset.Subset.refl _, 1, by norm_num, by simp [this]⟩
  let δ := s.inf' hne fun p => p.2.val
  have hδ : 0 < δ := (Finset.lt_inf'_iff hne).mpr fun p _ => p.2.property
  refine ⟨required ∪ s.image Prod.fst, Finset.subset_union_left, δ, hδ, fun x hx => ?_⟩
  obtain ⟨p, hp, hxU⟩ := mem_iUnion₂.mp (hs hx)
  have hδp : δ ≤ p.2.val := Finset.inf'_le _ hp
  refine ⟨p.1, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp), ?_⟩
  rcases hxU with h | h
  · exact Or.inl ((add_le_add_right hδp 1).trans ((lt_div_iff₀ (ht p.1)).mpr h).le)
  · exact Or.inr ((add_le_add_right hδp 1).trans ((lt_div_iff₀ (hv x hx p.1)).mpr h).le)

end Spectral

end VPVNP
end Computability
end OAI
