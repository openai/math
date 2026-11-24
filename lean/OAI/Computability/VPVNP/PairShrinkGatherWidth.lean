import OAI.Computability.VPVNP.PairShrinkPartyNative
import OAI.Computability.VPVNP.ShrinkFieldBounds

/-!
# Width of each row copied by the shrinking-party gather

An AB interval fits its demand, whose width is at most the largest old wire.
A surviving subdivision fits its selected supply field, including all the
selector bits. The resulting bound is uniform over the physical packet
addresses, the selected layout, and the subdivision index.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPartyNative

open Compression Compression.PackingData Compression.ShrinkMotif Compression.ShrinkEnergy
open MotifBlocks MotifGrid MotifConversion CompressorRecords CompressorRecords.ShrinkSlots
open ShrinkPartyColumns
open scoped Fin.CommRing

variable {a b g w : ℕ} {δ factor : ℝ} {K : Type*} [_root_.Field K]
  {X : State a (packingLaneBits a g)}
  {F : FixedBlock K demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
  {ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ} {sel : X.ShrinkSelection F}
  {m : X.packingData.Motif} {party : Fin 6} (J : Job X F ready sel m party w)

private noncomputable local instance : DecidableEq X.Base := Classical.decEq _
local notation "side" => selectedLayout X F sel
local notation "sub" => SlotLevel.Shape.subdivisions (levelShape (b := b) X)
local notation "count" => 2 ^ (Shrink.colors a) * 2 ^ a / 4

private theorem Job.abRow_bits_le (dir : Bool) (hit : party = if dir then 1 else 0)
    (i : Fin count) :
    (J.abRow dir hit i).bits.length ≤ X.maxWireWidth := by
  by_cases pos : 0 < (J.abRow dir hit i).bits.length
  · have bound := ab_bound X m J.arcFit J.bucketFit i J.arena J.nodes side dir (J.abHalf dir hit)
      J.first J.scratch.staging pos
    have old := X.packingData.abWidth_le (State.two_le_packingColors a) (Nat.two_pow_pos a)
      X.shrinkNumber X.packingWidth (fun _ ↦ X.width_le_maxWireWidth _) m
    exact (Nat.le_add_left ..).trans (bound.trans old)
  · omega

private theorem Job.supplyRow_bits_le (dir : Bool) (t : Fin 4)
    (hit : party = ShrinkSurvivingOperands.party side t dir) (i : Fin (sub t)) :
    (J.supplyRow dir t hit i).bits.length ≤ fieldFactor F * (X.maxWireWidth + 1) := by
  have bound := surviving_bound X side sub (branchWidth X F sel) (X.shrinkStateIndex ready side)
    m t dir (J.half dir t hit) J.arena J.node (J.scratch.surviving dir t)
    (J.allocation.row (ShrinkMotifOrder.stateNumber X m, t)) ready.count_pos i
  have term := X.packingData.shrinkTerm_bounds (State.two_le_packingColors a) (Nat.two_pow_pos a)
    X.shrinkNumber X.packingWidth (fun _ ↦ X.width_le_maxWireWidth _) F m (sel m)
  exact (Nat.le_add_left ..).trans (bound.trans (term.2 (side, t)).2)

/-- Each physical gather row copies at most a fixed block factor times the
largest old wire width plus one. This includes empty AB intervals. -/
theorem Job.row_bits_le (c : At party side) (i : Fin (frames count sub c.val)) :
    (J.row c i).bits.length ≤ (fieldFactor F + 1) * (X.maxWireWidth + 1) := by
  rw [Nat.add_mul, Nat.one_mul]
  rcases c with ⟨_ | ⟨dir, t⟩, h⟩
  · apply (J.abRow_bits_le (decide (party = 1)) _ i).trans
    omega
  · exact (J.supplyRow_bits_le dir t _ i).trans (Nat.le_add_right ..)

end PairSimulation.ShrinkPartyNative

end VPVNP
end Computability
end OAI
