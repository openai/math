import OAI.Hierarchy.DescentDatedStageObserved
import OAI.Hierarchy.DescentDatedOrdinaryProfileIssue
import OAI.Hierarchy.DescentDatedVenueFloor
import OAI.Hierarchy.DescentDatedVenueBelow

namespace OAI
/-! # Load the actual compact ballot and observe the chosen physical matcher on its resulting RAM -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPacking.PackedMatch
open DescentSixParty DescentSIMDLookup DescentColonies DescentPackedColony DescentKernelHistory.BitDescription
open DescentTerminalEpochDecoder DescentPackedProfileWindow DescentTerminalEpochChart DescentPackedProfileArchive
open DescentPackedProfileWide DescentPackedProfileInstall DescentGroupPeerOrder DescentStageEdgeReceipt
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentSixParty.StarKeys
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1000000
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (input : Dated.Operands) (base shelf : ℕ)
local notation "r" => v.prior
local notation "A" => v.prior.placement
local notation "a" => v.area
local notation "H" => 2^v.level
local notation "J" => v.schedule.groupCount v.age
local notation "M" => (a).lanesAt
local notation "M₀" => v.profileRepack.oldLanes
local notation "M₁" => v.profileRepack.newLanes
local notation "start" => v.profileRepack.endAddress base
local notation "src" => sourceBank shelf v.profileRepack.seats M₀
local notation "dst" => ((a).matcher v.old start).raw
variable (wide : Fintype.card v.prior.V ≤ 2^v.level)
local notation "names" => GroupStage.plane v.hostNumbers wide
local notation "rank" => groupRank ((Equiv.refl (Fin J)).toEmbedding.trans Fin.valEmbedding) ((names).trans Fin.valEmbedding)
local notation "rs" => (fun (h : Fin H) (j : Fin (A).degree)=>(r).venueRoster wide h (Fin.cast (r).branch j))
local notation "home" => scanHomeAt v.nonnegative (A).stage
local notation "color" => scanColorAt v.nonnegative (A).stage
variable {w : ℕ} {Pin : Type} (m : Memory w) (choice : (v.prior.placement.stage.result v.nonnegative).Choice)
    (entry : Source Pin) (z : Pin→Bool) (ext : DescentTerminalEpochBits.width entry.C ≤ v.area.shapeAt.digit)

theorem observed_venue_from_shelf (safe : (a).Space input w start) (oldRoster : input.roster=v.old)
    (stored : stageVenue r wide input M v.bitsPerField base ((r).venueRoster wide) m)
    (signed : ∀x : Block v.k,∀j : Fin (2*(A).cap),(input.wire x.val j.val).base+H*chunks J M≤base)
    (named : (A).SiteNamed rank) (mass : (A).wire*((A).z*v.gadget.b)*(A).cap<2^v.bitsPerField)
    (positions : J*H*2^v.k<2^w) (core : v.world.core.card<2^w)
    (seated : Fintype.card (NativePair v.world.graph v.world.core home color (A).cap)≤v.seats)
    (seats : v.profileRepack.seats=entry.seats) (bits : v.profileRepack.bits=DescentTerminalEpochBits.width entry.C)
    (pitch : M₁=M*(a).shapeAt.pairs) (oldPos : 0<M₀) (newPos : 0<M₁)
    (early : (src).Fits w base) (room : (dst).base+(dst).size<2^w)
    (actual : ∀j:Fin (DescentPackedProfileTape.slots entry.seats M₀),
      m (shelf+j.val)=((DescentPackedProfileTape.packed entry.pin z M₀ j.val).val:Word w)) :
    let load:=v.archivePhase base shelf w
    load.Runs m ∧ stageVenue r wide input M v.bitsPerField start ((r).venueRoster wide) (load.image m) ∧
    v.reachedReport input start wide (load.image m) choice entry z ext :=by
  intro load
  have part:=(v.archive_geometry base).1
  have init:start=base+v.profileRepack.endAddress 0:=v.profileRepack.translate base
  have low : base≤ start:=by omega
  have res:=stageVenue_below r wide input M v.bitsPerField base ((r).venueRoster wide) m (load.image m) stored signed
    (fun n hn=>v.archivePhase_frame base shelf w m early part room n (.inl hn) (.inl (hn.trans_le (low.trans part))))
  have old:=stageVenue_mono r wide input M v.bitsPerField base ((r).venueRoster wide) (load.image m) low res
  have raw:=v.archivePhase_issued base shelf w m early part room entry z seats bits pitch oldPos newPos ext actual
  refine ⟨v.archivePhase_runs base shelf w m early part room,old,?_⟩
  apply v.observed_venue input start wide (load.image m) choice entry z ext safe old named mass positions core seated
  simpa only [oldRoster] using raw


theorem observed_from_shelf (safe : (a).Space input w start) (oldRoster : input.roster=v.old)
    (stored : stageVenue r wide input M v.bitsPerField base ((r).venueRoster wide) m)
    (signed : ∀x : Block v.k,∀j : Fin (2*(A).cap),(input.wire x.val j.val).base+H*chunks J M≤base)
    (named : (A).SiteNamed rank) (mass : (A).wire*((A).z*v.gadget.b)*(A).cap<2^v.bitsPerField)
    (positions : J*H*2^v.k<2^w) (core : v.world.core.card<2^w)
    (seated : Fintype.card (NativePair v.world.graph v.world.core home color (A).cap)≤v.seats)
    (seats : v.profileRepack.seats=entry.seats) (bits : v.profileRepack.bits=DescentTerminalEpochBits.width entry.C)
    (pitch : M₁=M*(a).shapeAt.pairs) (oldPos : 0<M₀) (newPos : 0<M₁)
    (early : (src).Fits w base) (room : (dst).base+(dst).size<2^w)
    (actual : ∀j:Fin (DescentPackedProfileTape.slots entry.seats M₀),
      m (shelf+j.val)=((DescentPackedProfileTape.packed entry.pin z M₀ j.val).val:Word w)) :
    let load:=v.archivePhase base shelf w
    load.Runs m ∧ v.reachedReport input start wide (load.image m) choice entry z ext :=by
  have result:=v.observed_venue_from_shelf input base shelf wide m choice entry z ext safe oldRoster stored signed
    named mass positions core seated seats bits pitch oldPos newPos early room actual
  exact ⟨result.1,result.2.2⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
