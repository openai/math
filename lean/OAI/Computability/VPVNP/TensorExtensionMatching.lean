import OAI.Computability.VPVNP.ContractionClass
import OAI.Computability.VPVNP.GeneratorProducts
import OAI.Computability.VPVNP.SpectralMatching

/-!
# Prescribing added tensor values while extending the entire old spectrum

For the two cases of Theorem 2.4, the finite set of required generators
consists of the added star or the two added wires. The generator family
also contains every nonzero old restriction class. Multiplication folds
the old factors into one class before the contraction estimates are used.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u v
open Filter Topology
namespace WireTensor.SpectralPoint

open RestrictionClass
variable {k : Type u} {J : Type v} [Field k] [Fintype J] [Nonempty J]
variable (F : SpectralPoint k J)

/-- The contraction estimates for a finite family of added tensors imply
that one spectral point matches their prescribed values and extends the
original point on all old tensors. -/
theorem exists_extension_matching_of_rank {E : Type*} [Fintype E] [Nonempty E]
    (rank : RestrictionClass k (Option J) →+* ℕ) (hrank : Monotone rank)
    (extra : E → RestrictionClass k (Option J)) (cost : E → ℝ)
    (hExtra : ∀ i, extra i ≠ 0) (hcost : ∀ i, 0 < cost i)
    (upper : ∀ (x : RestrictionClass k J) (n : E → ℕ),
      F.contractionClassValue (embedOldClass x * ∏ i, extra i ^ n i) ≤
        ofSpectralPoint F x * ∏ i, cost i ^ n i)
    (balanced : ∀ (x : RestrictionClass k J) (e : ℕ), 0 < e →
      Tendsto (fun m : ℕ ↦ F.contractionClassValue ((embedOldClass x * ∏ i, extra i ^ e) ^ m)
        ^ (m : ℝ)⁻¹) atTop (𝓝 (ofSpectralPoint F x * ∏ i, cost i ^ e))) :
    ∃ H : SpectralPoint k (Option J), (∀ T, H.value (embedOld T) = F.value T) ∧
      ∀ i, ofSpectralPoint H (extra i) = cost i := by
  classical
  let : CharZero (RestrictionClass k (Option J)) := rank.charZero
  let Old := {x : RestrictionClass k J // x ≠ 0}
  let old : Old → RestrictionClass k J := Subtype.val
  let emb := (embedOldClass (k := k) (J := J)).toMonoidHom
  let eval := (ofSpectralPoint F).toMonoidHom
  let G : Old ⊕ E → RestrictionClass k (Option J) := Sum.elim (emb ∘ old) extra
  let target : Old ⊕ E → ℝ := Sum.elim (eval ∘ old) cost
  let required : Finset (Old ⊕ E) := Finset.univ.image Sum.inr
  have hG : ∀ i, G i ≠ 0 := by
    rintro (i | i)
    · change embedOldClass i.val ≠ 0
      exact fun h ↦ i.property (embedOldClass_injective (h.trans (map_zero _).symm))
    · exact hExtra i
  have ht : ∀ i, 0 < target i := by
    rintro (i | i)
    · have h := ofSpectralPoint_monotone F (orderBounds.one_le i.property)
      rw [map_one] at h
      exact zero_lt_one.trans_le h
    · exact hcost i
  have hmonomial (d : (Old ⊕ E) →₀ ℕ) :
      F.contractionClassValue (d.prod fun i n ↦ G i ^ n) ≤ d.prod fun i n ↦ target i ^ n := by
    dsimp only [G, target]
    rw [Spectral.fold_generatorMonomial emb old extra, Spectral.fold_generatorMonomial eval old cost]
    exact upper (∏ j ∈ d.support.toLeft, old j ^ d (.inl j)) (fun i ↦ d (.inr i))
  have hbalanced (s : Finset (Old ⊕ E)) (hs : required ⊆ s) (e : ℕ) (he : 0 < e) :
      Tendsto (fun m : ℕ ↦ F.contractionClassValue ((∏ i : s, G i ^ e) ^ m) ^ (m : ℝ)⁻¹)
        atTop (𝓝 (∏ i : s, target i ^ e)) := by
    have hall (i : E) : Sum.inr i ∈ s := hs (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hGfold := (Finset.prod_coe_sort s (fun i ↦ G i ^ e)).trans
      (Spectral.fold_generatorBalanced emb old extra s e hall)
    have htargetfold := (Finset.prod_coe_sort s (fun i ↦ target i ^ e)).trans
      (Spectral.fold_generatorBalanced eval old cost s e hall)
    rw [hGfold, htargetfold]
    exact balanced _ e he
  obtain ⟨H, hH, hmatch⟩ := Spectral.exists_matching_spectral_point orderBounds rank hrank G hG
    target ht required (Finset.univ_nonempty.image _) F.contractionClassValue
    F.contractionClassValue_monotone F.contractionClassValue_nonneg (fun x y ↦ (map_add _ x y).le)
    F.contractionClassValue_copies hmonomial hbalanced
  refine ⟨toSpectralPoint H hH, ?_, fun i ↦ ?_⟩
  · intro T
    apply NNReal.coe_injective
    change H (embedOldClass (ofTensor T)) = ofSpectralPoint F (ofTensor T)
    by_cases hz : ofTensor T = 0
    · rw [hz, map_zero, map_zero, map_zero]
    · exact hmatch (.inl ⟨ofTensor T, hz⟩)
  · obtain ⟨T, hT⟩ := ofTensor_surjective (extra i)
    rw [← hT, ofSpectralPoint_ofTensor, coe_toSpectralPoint_value, hT]
    exact hmatch (.inr i)

end WireTensor.SpectralPoint

end VPVNP
end Computability
end OAI
