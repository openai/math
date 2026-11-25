import OAI.Computability.BorderVNP.ShortenEpochEndpoints
import OAI.Computability.BorderVNP.ShortenEpochIdeal
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Canonical endpoint bins for the signed directions

For a compact window of the hyperbolic product and a prescribed multiset
of component speeds, the ideal position law and independent Haar-angle law
supply finite addresses with the properties used in (6.3): signed flips
permute addresses, preserve their probabilities, and preserve null-boundary
tests. Actual segment endpoints in a common bin are uniformly close for
both orientations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open MeasureTheory Set

variable {D : ℕ}

/-- The product of the ideal center law and the speed/angle law in one class. -/
noncomputable def configurationLaw (position : Measure (HyperbolicHost (Cube D)))
    (speed : Cube D → ℝ) := position.prod (idealDirectionLaw speed)

/-- Canonical bins on the actual hyperbolic configuration space, with each
`A_j` and the exact ideal probabilities exported together. -/
theorem canonical_crossing_bins {η : ℝ} (hη : 0 < η) :
    ∃ h > 0, ∀ s ∈ Ioc (0 : ℝ) h, ∀ (position : Measure (HyperbolicHost (Cube D))) [SFinite position]
      (speed : Cube D → ℝ) {K : Set (HyperbolicHost (Cube D))}, IsCompact K → ∃ (n : ℕ)
      (code : HyperbolicHost (Cube D) × Direction D ℂ → Fin n) (A : Fin D → Equiv.Perm (Fin n)),
      (∀ j c v, code (c, signedFlip j v) = A j (code (c,v))) ∧
      (∀ b, MeasurableSet (code ⁻¹' {b}) ∧ configurationLaw position speed (frontier (code ⁻¹' {b})) = 0) ∧
      (∀ j b, configurationLaw position speed (code ⁻¹' {A j b}) = configurationLaw position speed (code ⁻¹' {b})) ∧
      (∀ c ∈ K, ∀ v : Direction D ℂ, ‖v‖ = 1 → Function.Injective (fun j => A j (code (c,v)))) ∧
      ∀ c ∈ K, ∀ c' ∈ K, ∀ v v' : Direction D ℂ, ‖v‖ ≤ 1 → ‖v'‖ ≤ 1 →
        code (c,v) = code (c',v') → ∀ b : Bool,
          dist (shiftTo c (productLine (if b then v else -v) s))
            (shiftTo c' (productLine (if b then v' else -v') s)) ≤ η*s := by
  classical
  obtain ⟨h,hh,hhook⟩ := uniform_product_hooks (I := Cube D) (show 0 < η/3 by positivity)
  refine ⟨h,hh,?_⟩
  intro s hs position inst speed K hK
  let G := signedFactorGroup (Cube D)
  let H := HyperbolicHost (Cube D)
  let V := Direction D ℂ
  let μ := configurationLaw position speed
  let : Fintype G := Fintype.ofFinite _
  let : MulAction G H := {
    smul := fun _ c => c
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl }
  let : ContinuousConstSMul G H := ⟨fun _ => continuous_id⟩
  let : SFinite μ := by dsimp [μ, configurationLaw]; infer_instance
  let : SMulInvariantMeasure G (H × V) μ := {
    measure_preimage_smul := fun g {E} hE => by
      have hdir := measurePreserving_smul g (idealDirectionLaw speed)
      have h := (MeasurePreserving.id position).prod hdir
      exact h.measure_preimage hE.nullMeasurableSet }
  let S := K ×ˢ Metric.closedBall (0 : V) 1
  have hS : IsCompact S := hK.prod (isCompact_closedBall _ _)
  obtain ⟨bins,hnull,hfine,hend⟩ := exists_endpointBins (G := G) μ hS Prod.fst Prod.snd
    continuous_fst.continuousOn continuous_snd.continuousOn
    (fun x hx => by simpa [Metric.mem_closedBall] using hx.2) hη hs.1 (hhook s ⟨hs.1.le,hs.2⟩)
  let e := Fintype.equivFin bins.Address
  choose g hg using (exists_signedFactor_smul (D := D))
  let perm (j : Fin D) := e.symm.trans ((bins.perm (g j)).trans e)
  let code := e ∘ bins.code
  have hcode (a : bins.Address) : code ⁻¹' {e a} = bins.code ⁻¹' {a} := by
    ext x
    exact e.injective.eq_iff
  refine ⟨_,code,perm,?_,?_,?_,?_,?_⟩
  · intro j c v
    have he := bins.equivariant (g j) (c,v)
    change bins.code (c, g j • v) = _ at he
    rw [hg] at he
    simpa only [code, perm, Function.comp_apply, Equiv.trans_apply, Equiv.symm_apply_apply] using congrArg e he
  · intro b
    obtain ⟨a,rfl⟩ := e.surjective b
    rw [hcode]
    exact hnull a
  · intro j b
    obtain ⟨a,rfl⟩ := e.surjective b
    simp only [perm, Equiv.trans_apply, Equiv.symm_apply_apply, hcode]
    exact bins.ideal_mass μ (g j) a
  · intro c hc v hu j k hjk
    by_contra hj
    let vj := signedFlip j v
    let vk := signedFlip k v
    have hjn : ‖vj‖ = 1 := (signedFlip_orthonormal v hu).1 j
    have hkn : ‖vk‖ = 1 := (signedFlip_orthonormal v hu).1 k
    have he : bins.code (c,vj) = bins.code (c,vk) := by
      have e1 := bins.equivariant (g j) (c,v)
      have e2 := bins.equivariant (g k) (c,v)
      change bins.code (c,g j • v) = _ at e1
      change bins.code (c,g k • v) = _ at e2
      rw [hg] at e1 e2
      have e3 := e.injective (by simpa only [perm, code, Equiv.trans_apply, Function.comp_apply,
        Equiv.symm_apply_apply] using hjk)
      exact e1.trans (e3.trans e2.symm)
    have hdist := hfine (c,vj) ⟨hc,by simpa [Metric.mem_closedBall] using hjn.le⟩ (c,vk) he
    rw [dist_prod_same_left, dist_eq_norm] at hdist
    have hs : ‖vj - vk‖^2 = 2 := by
      rw [norm_sub_sq_real, hjn, hkn, signedFlip_orthogonal hj]
      norm_num
    nlinarith only [hs, hdist, norm_nonneg (vj-vk)]
  · intro c hc c' hc' v v' hv hv' he b
    apply hend (c,v) ⟨hc,by simpa [Metric.mem_closedBall] using hv⟩
      (c',v') ⟨hc',by simpa [Metric.mem_closedBall] using hv'⟩ (e.injective he) b

end Epoch

end BorderVNP
end Computability
end OAI
