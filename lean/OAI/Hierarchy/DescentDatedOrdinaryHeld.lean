import OAI.Hierarchy.DescentPriorOrdinaryHostCount
import OAI.Hierarchy.DescentDatedRegisterState
import OAI.Hierarchy.DescentOrdinaryVenueProof
import OAI.Hierarchy.DescentDatedRecordedOrdinaryVenue

namespace OAI
/-! # Both parts of the retained ordinary venue on the original issued date -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup DescentColonies
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
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

local notation "prev₀" m:arg => v.peerEntry root shelf header input count wires s d positive fit m

theorem peer_entry_low (m : Memory w) (j : ℕ) (hj : j < root) (beginAt : root ≤ rot)
    (paidAt : root ≤ v.donorEnd floor) : (prev₀ m) j=m j :=by
  let first:= (v.archivePhase root shelf w).image m
  let chosen:=((lay).nativePhase v.gadget positive input measure w floor fit.matcher).image first
  let assessed:=(d.afterMatcher v.payload v.seats input v.bitsPerField floor w).image chosen
  have fromRoot : root ≤ floor:=by change root ≤ v.profileRepack.endAddress root;rw [v.profileRepack.translate];omega
  have installed:=v.archivePhase_frame root shelf w m fit.source (v.archive_geometry root).1 fit.raw j
    (.inl hj) (.inl (hj.trans_le (fromRoot.trans (v.archive_geometry root).1)))
  have matched:=(lay).any_frame input w floor v.gadget positive measure fit.matcher first j (.inl (hj.trans_le fromRoot))
  have donor:=(d.afterMatcher_any v.payload v.seats input v.bitsPerField floor w chosen fit.donor).2 j
    (.inl (hj.trans_le beginAt))
  have built:=(v.before_signed_any floor s.parts s.adjacency fit.late.ranks fit.late.material assessed).2 j
    (.inl (hj.trans_le paidAt))
  exact built.trans (donor.trans (matched.trans installed))

theorem count_at_peer {M precision : ℕ} (m : Memory w) (oldFit : Fintype.card v.prior.V ≤ v.area.H)
    (newFit : Fintype.card v.target.V ≤ v.venue.hosts) (prior : stageVenue v.prior oldFit input M precision root
      (v.prior.venueRoster oldFit) m) (initial : m count.base=(Fintype.card v.prior.V:Word w))
    (loc : count.base < root) (birth : root ≤ rot) (paid : root ≤ v.donorEnd floor)
    (wiresRead : ∀(x:Block v.k)(j:Fin (2*v.prior.placement.cap)),
      (input.wire x.val j.val).base+v.area.H*chunks (v.schedule.groupCount v.age) M ≤ root)
    (degree : v.area.D=v.degree) (nextDegree : v.venue.degree=v.nextDegree) :
    v.afterPeer root shelf header input count wires s d positive fit m (PriorResetArchive.ordinary v floor).count.base
      =(Fintype.card v.target.V:Word w) :=by
  have low:=fun j hj=>v.peer_entry_low root shelf header input count wires s d positive fit m j hj birth paid
  have before:=paid.trans (v.signed_stage_paid floor).1
  have held:=stageVenue_below v.prior oldFit input M precision root (v.prior.venueRoster oldFit)
    m (prev₀ m) prior wiresRead low
  have headerRoom:=fit.late.peers
  change DescentOrdinaryVenueReturn.Room src (v.materialEnd floor) v.area.H v.area.D v.venue.hosts v.venue.degree w at headerRoom
  rw [degree,nextDegree] at headerRoom
  have seen:=v.ticket.return_header oldFit newFit input count (v.materialEnd floor) (prev₀ m) held before
    ((low _ loc).trans initial) headerRoom
  change (DescentOrdinaryVenueReturn.phase src (v.materialEnd floor) v.k v.area.H v.area.D v.venue.hosts v.venue.degree w).image
    (prev₀ m) (DescentOrdinaryPeerCount.newCount (v.materialEnd floor) v.area.H v.area.D v.venue.hosts v.venue.degree).base=_
  rw [degree,nextDegree]
  exact seen.2.2.2.1

variable {c z D k : ℕ} {bits : P→ℕ} {W : MarkedWorld F c P bits} {G : PoweredGadget F}
    {S : DescentCompiler.AtomSchedule} {q ε : ℝ} {age wire hist : ℕ}
    (r : Reached W G q ε S k age z D wire hist) (wide : Fintype.card r.V≤ v.venue.hosts)

theorem date_reached_venue (m : Memory w) (width : k=v.venue.k) (groups : S.groupCount age=v.venue.groups) (cap : r.placement.cap=v.venue.cap)
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
  have total : v.primitiveEnd floor ≤ v.fullEnd root :=
    (Nat.le_add_right (v.primitiveEnd floor) (2^v.countBits)).trans
      ((Nat.le_add_right _ v.area.batch).trans (Nat.le_add_right _ 1))
  have fresh : stageVenue r wide args v.venue.lanes v.venue.paidBits ready (r.venueRoster wide) counted :=
    stageVenue_below r wide args _ _ ready _ _ _ issued (fun x j=>by
      let jj:=Fin.cast (congrArg (2*·) cap) j
      obtain ⟨f,rows⟩:=v.venue.wire_room B vbase w (Fin.cast (congrArg (2^·) width) x) jj bank.venue.roof
      have sameRows := congrArg (fun g => v.venue.hosts*chunks g v.venue.lanes) groups
      exact (Nat.add_le_add_left (sameRows.le.trans rows) _).trans f.2.2) (fun j before=>by
      have one:=(v.counter_run floor archived fit.topology fit.limit).2 j (.inl ((before.trans_le mid).trans_le upper))
      have two:=(fit.late.primitive.2 returned).2 j (.inl (before.trans_le mid))
      exact one.trans (two.trans (v.return_below_venue floor B w bank current before)))
  have placed := v.venue.venue_lower B meterEnd vbase low roster hub
  have above : VenueFrom args D meterEnd := { placed with
    ids := fun j => (placed.actors.trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..) }
  exact stageVenue_mono r wide args _ _ ready _ _ (mid.trans (upper.trans total))
    (stageVenue_frame r wide args _ _ ready meterEnd _ counted _ fresh above
      (fun j hj=>(meter).counter_frame counted fit.counter j (ne_of_gt (small.trans_le hj)) (.inr hj)))


/-- The old venue supplies the true public count to the genuine successor
roster scan. Its returned count and the complete signed/paid raster survive
the exact ordinary CPU on the same input tape. -/
theorem date_ordinary_held (m : Memory w) (prev : DatePorts)
    (oldVenue : prev.held v.prior root m) (oldH : prev.venue.hosts=v.area.H)
    (oldIO : prev.io=input) (oldCount : prev.archive.count=count)
    (oldWidth : ∀(x:Block v.k)(j:Fin (2*v.prior.placement.cap)),
      (input.wire x.val j.val).base+v.area.H*chunks (v.schedule.groupCount v.age) prev.venue.lanes ≤ root)
    (priorAddr : count.base < root) (rotAt : root ≤ rot) (donorAt : root ≤ v.donorEnd floor)
    (priorDim : v.area.D=v.degree) (nextDim : v.venue.degree=v.nextDegree)
    (actual : B=v.reachedSources floor) (size : v.k=v.venue.k)
    (hosts : Fintype.card v.target.V ≤ v.venue.hosts) (groups : v.schedule.groupCount (v.age+1)=v.venue.groups)
    (cap : v.target.placement.cap=v.venue.cap) (meterAt : meterEnd ≤ vbase)
    (peerAt : meterEnd ≤ B.roster.base) (hubAt : meterEnd ≤ B.hub.base)
    (countAt : meterEnd≤(PriorResetArchive.ordinary v floor).count.base) (headerLow : header < meterEnd)
    (issued : stageVenue v.target hosts args v.venue.lanes v.venue.paidBits ready (v.target.venueRoster hosts)
      ((v.venue.phase B vbase w).image (v.beforeReturn root shelf header input count wires s d positive fit m))) :
    (DatePorts.ordinary v floor).held v.target (v.fullEnd root)
      (v.dateOutput root shelf header input count wires B s bank d positive fit m) :=by
  obtain ⟨capH,old,initial⟩:=oldVenue
  have oldFit : Fintype.card v.prior.V ≤ v.area.H:=capH.trans_eq oldH
  have stored : stageVenue v.prior oldFit input prev.venue.lanes prev.venue.paidBits root
      (v.prior.venueRoster oldFit) m:=by
    have storedBefore : ∃ fit : Fintype.card v.prior.V ≤ prev.venue.hosts,
        stageVenue v.prior fit prev.io prev.venue.lanes prev.venue.paidBits root (v.prior.venueRoster fit) m :=
      ⟨capH,old⟩
    rw [oldH,oldIO] at storedBefore
    exact storedBefore.choose_spec
  rw [oldCount] at initial
  have countR:=v.count_at_peer root shelf header input count wires s d positive fit m oldFit hosts
    stored initial priorAddr rotAt donorAt oldWidth priorDim nextDim
  have finalCount:=v.date_host_count root shelf header input count wires B s bank d positive fit m
    countAt headerLow countR
  have finalVenue:=v.date_reached_venue root shelf header input count wires B s bank d positive fit
    v.target hosts m size groups cap meterAt peerAt hubAt headerLow issued
  exact ⟨hosts,by simpa only [DatePorts.ordinary,←actual] using finalVenue,finalCount⟩


end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
