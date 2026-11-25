import OAI.Computability.BorderVNP.CoverLorentzFrames
import OAI.Computability.BorderVNP.CoverFrameOperator
import OAI.Computability.BorderVNP.CoverHeckeRotation
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

/-! # Topology and Borel structure of the quaternion frame quotient -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.Frame

open Matrix Set Hecke MeasureTheory TopologicalSpace

/-- The real frame group has the topology induced by its closed matrix embedding. -/
instance : LocallyCompactSpace SL := by
  let : LocallyCompactSpace Mat := inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  exact SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace

/-- The real frame group is second countable. -/
instance : SecondCountableTopology SL := by
  let : SecondCountableTopology Mat := inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  exact SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.secondCountableTopology

/-- The closed matrix embedding supplies a Polish topology. -/
instance : PolishSpace SL := by
  let : PolishSpace Mat := inferInstanceAs (PolishSpace (Fin 2 → Fin 2 → ℝ))
  exact SpecialLinearGroup.isClosedEmbedding_val.polishSpace

/-- Frame events are measured in the Borel sigma-algebra. -/
noncomputable instance : MeasurableSpace SL := borel SL

instance : BorelSpace SL := ⟨rfl⟩

/-- Each congruence lattice is countable. -/
instance frameGroup_countable (l : ℕ) : Countable (frameGroup l) := by
  let : Countable Order := (QuaternionAlgebra.equivTuple 2 0 3).injective.countable
  let : Countable Orderˣ := Units.val_injective.countable
  apply Function.Surjective.countable (f := (gammaSL l).rangeRestrict)
  rintro ⟨a, u, rfl⟩
  exact ⟨u, rfl⟩

/-- The frame lattice has finite intersection with every compact subset of the frame group. -/
theorem finite_inter_compact (l : ℕ) {K : Set SL} (hK : IsCompact K) :
    ((frameGroup l : Set SL) ∩ K).Finite := by
  let F : Set Mat := Subtype.val '' K
  have hF : IsCompact F := hK.image SpecialLinearGroup.isClosedEmbedding_val.continuous
  apply (((split_preimage_compact_finite hF).image split).preimage Subtype.val_injective.injOn).subset
  rintro A ⟨⟨u,rfl⟩, hu⟩
  exact ⟨u.val.val, ⟨gammaSL l u, hu, rfl⟩, rfl⟩

/-- The represented level group is closed in the real frame group. -/
theorem frameGroup_closed (l : ℕ) : IsClosed (frameGroup l : Set SL) :=
  (CompactlyGeneratedSpace.isClosed_iff_of_t2 _).mpr fun _ hK => (finite_inter_compact l hK).isClosed

/-- Two frame cosets are separated because the difference map detects the closed subgroup. -/
instance frameQuotient_t2 (l : ℕ) : T2Space (Cosets (frameGroup l)) := by
  apply (t2Space_iff_of_isOpenQuotientMap (coset_openQuotient (frameGroup l))).mpr
  have he : {v : SL × SL | coset (frameGroup l) v.1 = coset (frameGroup l) v.2} =
      (fun v : SL × SL => v.2 * v.1⁻¹) ⁻¹' (frameGroup l : Set SL) := by
    ext v
    exact Quotient.eq.trans QuotientGroup.rightRel_apply
  rw [he]
  exact (frameGroup_closed l).preimage (continuous_snd.mul continuous_fst.inv)

/-- The orbit quotient is second countable, since the frame projection is open. -/
instance frameQuotient_secondCountable (l : ℕ) : SecondCountableTopology (Cosets (frameGroup l)) :=
  Topology.IsOpenQuotientMap.secondCountableTopology (coset_openQuotient (frameGroup l))

/-- The compact Hausdorff frame quotient is metrizable. -/
theorem frameQuotient_metrizable (l : ℕ) : MetrizableSpace (Cosets (frameGroup l)) := inferInstance

/-- The quotient measurable structure is exactly the Borel sigma-algebra. -/
theorem frameQuotient_borel (l : ℕ) : BorelSpace (Cosets (frameGroup l)) := inferInstance

end Cover.Frame

end BorderVNP
end Computability
end OAI
