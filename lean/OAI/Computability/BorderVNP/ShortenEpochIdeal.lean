import OAI.Computability.BorderVNP.ShortenEpochSignedGroup
import OAI.Computability.BorderVNP.ShortenEpochBins
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Group.Circle
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Ideal direction counts from independent Haar frames

Uniformly permute the speeds, then sample an independent Haar angle in every
surface factor. A sign change is a rotation by half a turn and preserves Haar
measure, and reordering an independent product of identical angular laws
preserves its law. Hence every signed coordinate permutation preserves the
ideal direction law, even if some speeds vanish.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Classical

noncomputable section

/-- Haar probability for the component angle. -/
noncomputable def angularHaar : Measure Circle :=
  Measure.haarMeasure (⟨⟨univ, isCompact_univ⟩, by simp⟩ : TopologicalSpace.PositiveCompacts Circle)

instance : IsProbabilityMeasure angularHaar :=
  ⟨Measure.haarMeasure_self (K₀ := ⟨⟨univ, isCompact_univ⟩, by simp⟩)⟩

instance : Measure.IsMulLeftInvariant angularHaar := by unfold angularHaar; infer_instance

variable {I : Type*} [Fintype I]

private noncomputable def angles (I : Type*) [Fintype I] := Measure.pi (fun _ : I => angularHaar)

private def rotateAngles (e : Equiv.Perm I) (s : I → Bool) (a : I → Circle) (i : I) : Circle :=
  (if s i then -1 else 1) * a (e i)

private theorem preserving_rotateAngles (e : Equiv.Perm I) (s : I → Bool) :
    MeasurePreserving (rotateAngles e s) (angles I) (angles I) := by
  have hperm : MeasurePreserving (fun (a : I → Circle) i => a (e i)) (angles I) (angles I) := by
    convert measurePreserving_piCongrLeft (α := fun _ : I => Circle)
      (fun _ : I => angularHaar) e.symm using 1
    · funext a i
      simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    all_goals rfl
  have hrot : MeasurePreserving (fun (a : I → Circle) i => (if s i then -1 else 1) * a i)
      (angles I) (angles I) :=
    measurePreserving_pi (fun _ : I => angularHaar) (fun _ : I => angularHaar)
      (fun i => measurePreserving_mul_left angularHaar (if s i then -1 else 1))
  exact hrot.comp hperm

/-- Tangent vector in a chosen permutation of the speeds and component angles. -/
def fromAngles (speed : I → ℝ) (f : Equiv.Perm I) (a : I → Circle) :
    PiLp 2 fun _ : I => ℂ := WithLp.toLp 2 fun i => speed (f i) • (a i : ℂ)

omit [Fintype I] in
private theorem measurable_fromAngles (speed : I → ℝ) (f : Equiv.Perm I) :
    Measurable (fromAngles speed f) :=
  (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr fun i => by
    exact (measurable_const_smul (speed (f i))).comp
      (Circle.measurable_coe.comp (measurable_pi_apply (X := fun _ : I => Circle) i)))

omit [Fintype I] in
private theorem factorPerm_fromAngles (speed : I → ℝ) (e f : Equiv.Perm I) (s : I → Bool)
    (a : I → Circle) :
    factorPerm e s (fromAngles speed f a) =
      fromAngles speed (e.trans f) (rotateAngles e s a) := by
  ext1 i
  cases hs : s i
  · change (if s i then -_ else _) = speed (f (e i)) • ((rotateAngles e s a i : Circle) : ℂ)
    simp [rotateAngles, hs, fromAngles]
  · change (if s i then -_ else _) = speed (f (e i)) • ((rotateAngles e s a i : Circle) : ℂ)
    simp [rotateAngles, hs, fromAngles]

/-- The mixture over all speed orderings of independent Haar component angles. -/
noncomputable def idealDirectionLaw (speed : I → ℝ) : Measure (PiLp 2 fun _ : I => ℂ) :=
  (Fintype.card (Equiv.Perm I) : ℝ≥0∞)⁻¹ •
    ∑ f : Equiv.Perm I, (angles I).map (fromAngles speed f)

instance (speed : I → ℝ) : IsProbabilityMeasure (idealDirectionLaw speed) := by
  classical
  constructor
  have hun (f : Equiv.Perm I) : ((angles I).map (fromAngles speed f)) univ = 1 := by
    rw [Measure.map_apply (measurable_fromAngles _ _) MeasurableSet.univ, preimage_univ]
    dsimp [angles]; simp
  simp [idealDirectionLaw, Measure.finsetSum_apply, hun]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp)

/-- The signed factor group preserves the manuscript's actual ideal law. -/
instance (speed : I → ℝ) : SMulInvariantMeasure (signedFactorGroup I) _
    (idealDirectionLaw speed) := by
  classical
  constructor
  intro g S hS
  obtain ⟨e, sign, hg⟩ := g.property
  change idealDirectionLaw speed (g.val ⁻¹' S) = _
  rw [hg]
  have hp := (factorPerm_isometry e sign).continuous.measurable
  have hterm (f : Equiv.Perm I) :
      ((angles I).map (fromAngles speed f)) ((factorPerm e sign) ⁻¹' S) =
        ((angles I).map (fromAngles speed (e.trans f))) S := by
    rw [Measure.map_apply (measurable_fromAngles _ _) (hS.preimage hp),
      Measure.map_apply (measurable_fromAngles _ _) hS]
    have he : (fromAngles speed f) ⁻¹' ((factorPerm e sign) ⁻¹' S) =
        (rotateAngles e sign) ⁻¹' (fromAngles speed (e.trans f) ⁻¹' S) := by
      ext a
      change (factorPerm e sign (fromAngles speed f a) ∈ S) ↔ _
      rw [factorPerm_fromAngles]
      rfl
    rw [he]
    exact (preserving_rotateAngles e sign).measure_preimage (hS.preimage (measurable_fromAngles _ _)).nullMeasurableSet
  simp only [idealDirectionLaw, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul,
    hterm]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight e) (fun f => (angles I).map (fromAngles speed f) S)

/-- The mean ideal bin counts are invariant for each of the crossing
permutations, for the actual Haar-angle mixture. -/
theorem ideal_bin_invariant (speed : I → ℝ)
    (bins : DirectionBins (signedFactorGroup I) (PiLp 2 fun _ : I => ℂ))
    (g : signedFactorGroup I) (b : bins.Address) :
    idealDirectionLaw speed (bins.code ⁻¹' {bins.perm g b}) =
      idealDirectionLaw speed (bins.code ⁻¹' {b}) :=
  bins.ideal_mass _ g b

end

end Epoch

end BorderVNP
end Computability
end OAI
