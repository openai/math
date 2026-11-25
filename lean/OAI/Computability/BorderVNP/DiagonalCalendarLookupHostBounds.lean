import OAI.Computability.BorderVNP.DiagonalCalendarLookupHostWords
import OAI.Computability.BorderVNP.DiagonalCalendarLookupHostAddressBounds
import OAI.Computability.BorderVNP.DiagonalCalendarLookupHostCapacity

/-! # Numerical inputs of the attained host writer on the original calendar -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Diagonal.ExternalSew Cover Packing Packing.DeckGrid Crossing Branch Epoch PackedHistoryCircuit
open PackedHistoryCircuit.Normalized SelectedSchedule TeamScales TeamContraction ProcessorSlots
open VPVNP FieldProcessor RoutingISA GeometryAdvice GeometryFrameEncoding
open DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins
open scoped Classical BorderVNP.Epoch.Cube

set_option maxRecDepth 8200
set_option maxHeartbeats 4000000

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {paid : PaidIdentity F D m}
    {S : SiteSchedule paid} {cube : FixedCube K} {extra E p Q breadth sourcePower : ℕ}
    {scales : EpochScales S (cube.pred+1) extra}
    {b : JointSchedule.{0} scales (E+1) (max (5*(E+2)) p) Q 3076 (breadth+10) (sourcePower+1)}
    {φ : K →+* F} {q : ℕ} {hm : 0 < «m»} {header C A₀ a B₀ b₀ J j coeff addr power cut : ℕ}
    {adv : ℕ → ℕ} {c charge factor l : ℕ}
    (cal : SignedCalendarAt cube b φ q hm header C A₀ a B₀ b₀ J j coeff addr power cut adv c charge factor (l+1))
    (oper : FrozenExecutionAt cube b φ q adv c charge header (hm:=hm) (l+1)) (qpos : 1 ≤ Q)
    (position : (Fin (Fintype.card (Cube D)) → Deck (CoverScale.initialDepth (Cube D)
      (stretch b.ρ (l+1)) (l+1)-1+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField paid (φ ∘ cube.table) q l (stretch b.σ (l+1)) ord}
    (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (b.physical.teamsPred (l+1)+1) (stretch b.ρ (l+1))
      (b.physical.multBits (l+1)) (b.physical.tally (l+1)) (b.physical.word (l+1))
      (adv (adviceScale b.σ b.ρ (l+1))+6))
    (chargeFit : reader.charge ≤ c*(adv (adviceScale b.σ b.ρ (l+1))+1)^charge)

/-- The memory and field bounds for the host source as it was written. The
last predicate specifies the space occupied by the actual original rows at
each receiving cell. -/
structure FrozenLookupHostBounds (ownerWord fieldWord w sourceBase candidates origin cables headerBase
    teams processors fields literal cells stride : ℕ) (cellCapacity : Prop) : Prop where
  /-- An owner index fits the encoded field word. -/
  ownerWidth : ownerWord≤fieldWord
  /-- A geometry field fits the machine word. -/
  wordFit : fieldWord≤w
  /-- All candidate records precede the geometry. -/
  reserve : sourceBase+7*candidates≤origin
  /-- The complete five-word cable rectangle precedes the cube header. -/
  endGeo : origin+5*cables≤headerBase
  /-- The geometry starts at an encodable word. -/
  geoFit : origin<2^w
  /-- The number of teams fits the word address range. -/
  teamsFit : teams≤2^w
  /-- The number of processors fits the word address range. -/
  processorFit : processors≤2^w
  /-- The field count fits the word address range. -/
  fieldsFit : fields≤2^w
  /-- The literal length has a machine representation. -/
  literalFit : literal<2^w
  /-- The number of cells fits the word address range. -/
  cellsFit : cells≤2^w
  /-- The cell stride fits the word address range. -/
  strideFit : stride≤2^w
  /-- Every cell accommodates its supplied words, private gap, and assigned originals. -/
  capacity : cellCapacity

private theorem collectHostBounds {ownerWord fieldWord w sourceBase candidates origin cables head
    teams processors fields literal cells stride : ℕ} {capacity : Prop}
    (widths : ownerWord≤fieldWord ∧ fieldWord≤w ∧ teams≤2^w ∧ processors≤2^w ∧ fields≤2^w ∧
      literal<2^w ∧ cells≤2^w ∧ stride≤2^w)
    (place : sourceBase+7*candidates≤origin ∧ origin+5*cables≤head ∧ origin<2^w)
    (room : capacity) :
    FrozenLookupHostBounds ownerWord fieldWord w sourceBase candidates origin cables head teams processors
      fields literal cells stride capacity := by
  obtain ⟨owner,word,team,proc,fs,lit,cs,step⟩ := widths
  exact ⟨owner,word,place.1,place.2.1,place.2.2,team,proc,fs,lit,cs,step,room⟩

/-- All numerical arguments for the actual host source at this selected
history, including the descriptions occupying each individual planner cell. -/
noncomputable abbrev SignedCalendarAt.frozenLookupHostBounds (values : _) (hist : _) :=
  collectHostBounds
    (cal.frozenLookupHostWordBounds oper qpos position chart reader chargeFit values hist)
    (cal.frozenLookupHostAddressBounds oper.grid qpos position chart reader chargeFit oper.routing)
    (cal.frozenLookupHostCapacity oper.grid qpos position chart reader chargeFit values hist)

end Diagonal

end BorderVNP
end Computability
end OAI
