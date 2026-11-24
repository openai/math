import OAI.Computability.VPVNP.PairShrinkNodeLabelBudget
import OAI.Computability.VPVNP.PairTraversalRoles
import OAI.Computability.VPVNP.PairSelectedKernelReaders
import OAI.Computability.VPVNP.CompressorLevelCounts

/-! # Histogram headroom at a selected shrinking level

The tag determines the scheduled shrinking pass. Its resident map witnesses
give the exponents of the selected reader, and the branch width bound controls
the number of copies in each resident map.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open Compression Compression.ShrinkMotif CompressorRecords LocalHistory TraversalRoles

variable {k K : Type*} [Field k] [CommRing K] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → K) (hf : B.IsSolution f)

local notation "reader" v => originReader B f hf (SelectedLevel.origin v) (SelectedLevel.term v)

/-- Each coordinate of the exponent vector contributed by one shrinking
vertex fits the quadratic histogram allowance. -/
theorem level_exponent_le_square (v : SelectedLevel B f hf) (shrink : tagLevel B f hf v = .shrink)
    {n : ℕ} (hn : 1 ≤ n) (width : v.input.maxWireWidth ≤ n)
    (large : ∀ j : Fin S.steps,
      2 * (MapResidentRows.capacity (S.degreeExponent j.castSucc) * fieldFactor B.shrink) ≤ n) :
    ∀ u b a x l, ((reader v).witness u a b).exponents x l ≤ n ^ 2 := by
  rcases v with ⟨deg, lanes, outDeg, outLanes, Y, p, origin, term, tape⟩
  cases origin with
  | shrink j eqn Y =>
    subst lanes
    intro u b a x l
    exact MapWitness.exponent_le_square B f hf j Y term u a b x l hn width (large j)
  | refresh => cases shrink

/-- At every shrinking vertex on the chosen execution, the input width
estimate of the branch suffices for the per-coordinate histogram bound. -/
theorem selected_exponent_le_square {lanes : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ lanes)
    (X : State (S.degreeExponent 0) lanes) (z : (B.execute f hf T hT X).Choices)
    (i : Fin (executeLevels B f hf T hT X z).length)
    (shrink : tagLevel B f hf (executeLevels B f hf T hT X z)[i] = .shrink)
    {n : ℕ} (hn : 1 ≤ n) (width : B.growthConstant ^ T * (X.maxWireWidth + 1) ≤ n)
    (large : ∀ j : Fin S.steps,
      2 * (MapResidentRows.capacity (S.degreeExponent j.castSucc) * fieldFactor B.shrink) ≤ n) :
    ∀ u b a x l,
      ((reader ((executeLevels B f hf T hT X z).get i)).witness u a b).exponents x l ≤ n ^ 2 :=
  level_exponent_le_square B f hf _ shrink hn
    ((executeLevels_limits B f hf T hT X z _ (List.getElem_mem _)).2.trans width) large

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
