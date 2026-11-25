import OAI.Hierarchy.DescentVenueRosterDefinition
import OAI.Hierarchy.DescentDatedOrdinaryDateAny
import OAI.Hierarchy.DescentDatedVenueBelow
import OAI.Hierarchy.DescentDatedVenueFloor
import OAI.Hierarchy.DescentNormalizedVenueLower
import OAI.Hierarchy.DescentStageVenueWireRoom

namespace OAI
/-! # The reached successor remains available after the private ordinary count update -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup DescentColonies DescentCompiler
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (root shelf header : ℕ)
  (input : Dated.Operands) (count : Bank) (wires : v.signed.Input) (B : StageVenueTail.Sources)
  {w : ℕ} (s : ResultSteps w) (bank : v.ResultRoom (v.stageStart root) B w) (d : DonorDate) (positive : 0< d.exponent)
local notation "floor" => v.stageStart root
local notation "lay" => d.schedule v.payload v.seats v.bitsPerField
local notation "rot" => (lay).rotationEnd input.roster floor
local notation "measure" => (⟨v.prior.placement.wire,v.prior.placement.z,v.prior.placement.hist⟩:Dated.Measures)
local notation "src" => (⟨count,input.roster,input.hubs⟩:DescentOrdinaryVenueReturn.Sources)
local notation "meter" => d.counter v.payload rot header
local notation "meterEnd" => (meter).endAddr
local notation "vbase" => v.rasterEnd floor
local notation "ready" => v.metaStart floor
local notation "args" => v.venue.operands B vbase
variable (fit : Room v root shelf header input count wires s d)

def beforeReturn (m : Memory w) : Memory w :=
  let t:=(v.archivePhase root shelf w).image m
  let t:=((lay).nativePhase v.gadget positive input measure w floor fit.matcher).image t
  let t:=(d.afterMatcher v.payload v.seats input v.bitsPerField floor w).image t
  let t:=(v.beforeSignedMaterial floor s.parts s.adjacency w).image t
  let t:=(DescentOrdinaryVenueReturn.phase src (v.materialEnd floor) v.k v.area.H v.area.D v.venue.hosts v.venue.degree w).image t
  let t:=(v.mark floor input w).image t
  let t:=(v.signed.phase wires (v.markEnd floor) w).image t
  s.paid.image (s.arguments.image t)

variable {c z D : ℕ} {bits : P→ℕ} {W : MarkedWorld F c P bits} {G : PoweredGadget F}
    {S : AtomSchedule} {q ε : ℝ} {age wire hist : ℕ}
    (r : Reached W G q ε S v.venue.k age z v.venue.degree wire hist) (wide : Fintype.card r.V≤ v.venue.hosts)

theorem date_venue (m : Memory w) (groups : S.groupCount age=v.venue.groups) (cap : r.placement.cap=v.venue.cap)
    (low : meterEnd≤ vbase) (roster : meterEnd≤ B.roster.base) (hub : meterEnd≤ B.hub.base) (small : header< meterEnd)
    (issued : stageVenue r wide args v.venue.lanes v.venue.paidBits ready (r.venueRoster wide)
      ((v.venue.phase B vbase w).image (v.beforeReturn root shelf header input count wires s d positive fit m))) :
    stageVenue r wide args v.venue.lanes v.venue.paidBits (v.fullEnd root) (r.venueRoster wide)
      (v.dateOutput root shelf header input count wires B s bank d positive fit m) :=by
  let current:=v.beforeReturn root shelf header input count wires s d positive fit m
  let returned:=(v.returnPhase floor B w bank).image current
  let archived:=s.primitive.image returned
  let counted:=(v.counter floor w).image archived
  have mid : ready≤ v.operandEnd floor:=by
    have after₁:v.metaStart floor≤ v.metaEnd floor:=by rw [metaEnd,v.metadata.ordinary_translate];omega
    have after₂:v.metaEnd floor≤ v.operandEnd floor:=by rw [operandEnd,v.operandBook.affine];omega
    exact after₁.trans after₂
  have upper:=fit.late.primitive.1
  have total : v.primitiveEnd floor ≤ v.fullEnd root := by
    change _ ≤ v.primitiveEnd floor + _ + _ + 1
    exact ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ 1)
  have fresh : stageVenue r wide args v.venue.lanes v.venue.paidBits ready (r.venueRoster wide) counted :=
    stageVenue_below r wide args _ _ ready _ _ _ issued (fun x j=>by
      let jj:=Fin.cast (congrArg (2*·) cap) j
      obtain ⟨f,rows⟩:=v.venue.wire_room B vbase w x jj bank.venue.roof
      have covered := (congrArg (fun n => v.venue.hosts * chunks n v.venue.lanes) groups).le.trans rows
      exact (Nat.add_le_add_left covered _).trans f.2.2) (fun j before=>by
      have one:=(v.counter_run floor archived fit.topology fit.limit).2 j (.inl ((before.trans_le mid).trans_le upper))
      have two:=(fit.late.primitive.2 returned).2 j (.inl (before.trans_le mid))
      exact one.trans (two.trans (v.return_below_venue floor B w bank current before)))
  have above:=v.venue.venue_lower B meterEnd vbase low roster hub
  exact stageVenue_mono r wide args _ _ ready _ _ (mid.trans (upper.trans total))
    (stageVenue_frame r wide args _ _ ready meterEnd _ counted _ fresh above
      (fun j hj=>(meter).counter_frame counted fit.counter j (ne_of_gt (small.trans_le hj)) (.inr hj)))

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
