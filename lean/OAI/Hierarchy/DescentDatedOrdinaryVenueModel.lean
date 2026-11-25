import OAI.Hierarchy.DescentRecordedOrdinaryVenue
import OAI.Hierarchy.DescentDatedOrdinaryCountRoof
import OAI.Hierarchy.DescentDatedOrdinarySignedPhase
import OAI.Hierarchy.DescentPaidSweepHeldTariff
import OAI.Hierarchy.DescentDatedOrdinaryFundedRaster

namespace OAI
/-! # The clipped ordinary reached raster at the actual addresses of its date -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPacking.PackedMatch.Local.Stage DescentRawCablePanel DescentSIMDLookup DescentDyadicSpan
open DescentPaidResidentCount DescentOrdinaryAtomFieldRAM DescentActorRaster DescentPackedColony
open DescentDatedAddressBook DescentPacking DescentStageEdgeReceipt DescentOrdinaryRasterReturn
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentColonies
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P:Type} [Field F](v:PhysicalOrdinary F P)(floor:ℕ)
local notation "a" => v.area
local notation "d" => v.venue
local notation "work" => v.rasterLanes
local notation "start" => v.endAddress floor
local notation "prep" => StageVenueTail.OrdinaryRaster.prepared (a) (d) work start
local notation "stop" => StageVenueTail.OrdinaryRaster.sweep (a) (d) work start
local notation "R" => StageVenueTail.OrdinaryRaster.shapes (a)
local notation "A" => StageVenueTail.OrdinaryRaster.donors (a)
local notation "n" => StageVenueTail.OrdinaryRaster.nameBits (a)
local notation "paths" => StageVenueTail.OrdinaryRaster.paths (a)
local notation "dim" => StageVenueTail.OrdinaryRaster.dims (a) (d) work
local notation "p" => v.materialEnd floor
local notation "rawP" => Sweep.paidBank prep R A (a).cap (d).paidBits n (a).H (a).G work
local notation "rawA" => Sweep.aliveBank prep R A (a).cap (d).paidBits n (a).H (a).G work
local notation "counter" => DescentOrdinaryPeerCount.newCount p (a).H (a).D (d).hosts (d).degree
def reachedRaster : DescentOrdinaryRasterReturn.Sources:=⟨rawP,rawA,counter⟩

def reachedWire (x j:ℕ):Bank:=
  if hx:x<v.signed.blocks then
    if hj:j<2*v.signed.cap then v.signed.page (v.markEnd floor) ⟨x,hx⟩ ⟨j,hj⟩ else ⟨0,0⟩
  else ⟨0,0⟩

theorem reachedWire_at (x:Fin v.signed.blocks)(j:Fin (2*v.signed.cap)):
    v.reachedWire floor x.val j.val=v.signed.page (v.markEnd floor) x j:=by simp [reachedWire,x.isLt,j.isLt]

def reachedSources:StageVenueTail.Sources:=
  ⟨DescentOrdinaryPeerRows.peers p (a).H (a).D (d).hosts (d).degree,
    DescentOrdinaryVenueReturn.hubs p (a).H (a).D (d).hosts (d).degree,
    actorBank dim stop,paidBank dim stop,v.reachedWire floor⟩

theorem reachedEnd :v.rasterEnd floor=DescentOrdinaryRasterReturn.roof dim stop:=rfl

theorem reachedDate (blocks:(d).k=v.k)(groups:(d).groups=v.schedule.groupCount (v.age+1))
    (degree:(d).degree=v.nextDegree)(cap:(d).cap=v.target.placement.cap)(paired:(d).aliveLanes=(d).paidLanes):
    (⟨v.k,(d).hosts,v.schedule.groupCount (v.age+1),v.nextDegree,v.target.placement.cap,(d).paidBits,
      (d).paidLanes,(d).signedLanes,(d).paidLanes,(d).lanes⟩:StageVenueTail.Date)=d:=by
  calc
    _=⟨(d).k,(d).hosts,(d).groups,(d).degree,(d).cap,(d).paidBits,(d).aliveLanes,
        (d).signedLanes,(d).paidLanes,(d).lanes⟩:=by rw [blocks,groups,degree,cap,paired]
    _=d:=rfl

theorem reachedPitch:StageVenueTail.OrdinaryRaster.shapes (a)=
    (2^(v.k+1)-1)*(2^(DescentHostDegree.packExponent 20 v.prior.placement.degree)+2):=rfl

theorem reachedLower :
    v.donorEnd floor≤(v.reachedSources floor).roster.base ∧ v.donorEnd floor≤(v.reachedSources floor).hub.base:=by
  have early:=(v.signed_stage_paid floor).1
  constructor <;> apply early.trans
  · change p≤DescentOrdinaryPeerChart.out (DescentOrdinaryPeerRows.fixed p (a).H (a).D) (a).H ((d).hosts*(d).degree)
    simp only [DescentOrdinaryPeerChart.out,DescentOrdinaryPeerRows.fixed]
    omega
  · change p≤DescentOrdinaryPeerCount.roof p (a).H (a).D (d).hosts (d).degree+2*DescentDyadicSpan.span (d).hosts
    simp only [DescentOrdinaryPeerCount.roof,DescentOrdinaryPeerRows.endAddress,DescentOrdinaryPeerChart.top,
      DescentOrdinaryPeerChart.out,DescentOrdinaryPeerRows.fixed]
    omega

theorem rasterBanks_same:v.reachedRaster floor=v.paidRasterBanks floor:=rfl

abbrev reachedPaid {w:ℕ}(B:v.FundedInputs)(input:Dated.Operands)(ok:v.FundedRoom floor B input w):NativePhase w:=
  v.fundedRaster floor B input w ok

theorem reachedPaid_any {w:ℕ}(B:v.FundedInputs)(input:Dated.Operands)(ok:v.FundedRoom floor B input w)(m:Memory w):
    (v.reachedPaid floor B input ok).Runs m ∧
    ∀x,x<start ∨ v.rasterEnd floor≤x→(v.reachedPaid floor B input ok).image m x=m x:=
  v.fundedRaster_run floor B input w ok m

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
