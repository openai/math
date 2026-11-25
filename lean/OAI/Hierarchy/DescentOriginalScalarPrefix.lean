import OAI.Hierarchy.DescentPhysicalOriginalZeroHalo
import OAI.Hierarchy.DescentNamedOriginalScalarFit

namespace OAI
/-! # Original scalar words after the dated donor tables have executed -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSixParty.Chronology DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {a : PhysicalReset} {floor w N : ℕ} (u : a.DateInputs floor w)
variable (R : u.MeasuredChannels N) (m : Memory w) (seen : CaptureRoom R m)
set_option quotPrecheck false
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "s" => (v).sheets
local notation "p" => (v).front.peer
local notation "area" => ((v).remap b).endAddress

/-- The fixed instruction arguments of the original public and private numberers. -/
structure OriginalScalarLayout : Prop where
  degree : u.numbered.degree=(p).oldDegree
  zero : ∀x,u.numbered.zero x=(v).originalZero b x.val
  publicZero : ∀x,u.numbered.sources.zero x=(v).originalZero b x.val
  halo : ∀x,u.numbered.halo x=(v).originalHalo b
  self : ∀x,u.numbered.sources.self x=((v).originalPrior b u.numbered.signedSlots).self x
  shape : ∀x,u.numbered.sources.shape x=((v).originalPrior b u.numbered.signedSlots).shape x
  haloRoom : (p).oldDegree < 2^(s).haloBits
  selfRoom : (p).oldDegree < 2^(s).shortBits
  shapeRoom : (p).shapes ≤ 2^(s).shortBits

def measuredScalar (j : Fin 4) (h : Fin (s).hosts) : Cell (s).metaBits :=
  ⟨DescentResetPeerJointPacked.Aux.value (p).shapes R.names R.prior R.near h j,
    DescentResetPeerJointPacked.Aux.value_lt (p).shapes R.names R.prior R.near h j seen.distinct
      seen.shapes seen.keys seen.previousSelf⟩

theorem original_prefix_sources (ok : u.Ready) (degree : u.numbered.degree=(p).oldDegree) :
    DescentResetOriginalZeroHalo.Sources (originalNumberBase a floor) (s).hosts (s).groups (s).lanes (s).metaBits
      (s).zeroBits (s).shortBits (s).haloBits (p).oldDegree (originalScalarBank a floor 0)
      (originalScalarBank a floor 1) (u.measuredScalar R m seen 0) (u.measuredScalar R m seen 1)
      (u.numbered.prefixOutput area (u.masked.image (u.privateResult m))) := by
  have cuts := (s).originalDonors.cuts ((s).inputDonorsBase area)
  have roof : (s).inputDonorsBase area < 2^w := (cuts.1.trans (cuts.2.1.trans cuts.2.2)).trans_lt ok.numbers.donor.room
  let state := (originalNumberPhase a floor w).image (u.coordinateResult m)
  have same :
      (u.numbered.scalarPhase area w).image (u.coordinateResult m) = state := by
    dsimp only [CandidateSheets.OriginalInputs.scalarPhase, state, originalNumberPhase, originalNumberBase]
    rw [degree]
  have native := (u.original_numbers R m ok seen roof).2.1
  have keep := ((s).originalDonors.any ((s).inputDonorsBase area) u.numbered.sensor
    ok.numbers.donor state).2.2
  apply DescentResetOriginalZeroHalo.Sources.transfer _ _ _ _ _ _ _ _ _ native ((v).originalAux_fits b 0 ok.packed) ((v).originalAux_fits b 1 ok.packed) roof
  intro i earlier
  change (s).originalDonors.after ((s).inputDonorsBase area) u.numbered.sensor
    ((u.numbered.scalarPhase area w).image (u.coordinateResult m)) i=state i
  rw [same]
  exact keep i (.inl earlier)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
