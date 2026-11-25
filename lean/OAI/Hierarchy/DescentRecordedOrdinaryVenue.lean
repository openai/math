import OAI.Hierarchy.DescentStageVenuePaidPages
import OAI.Hierarchy.DescentReachedPaidFundedReturn
import OAI.Hierarchy.DescentReachedOrdinaryReturn
import OAI.Hierarchy.DescentOrdinaryVenueProof
import OAI.Hierarchy.DescentStageVenueAny

namespace OAI
/-! # The genuine clipped funds, presence, signed and peer fields in one next ordinary venue -/
namespace Hierarchy.DescentLocalArchiveOrder
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler DescentStageEdgeReceipt
open DescentCableDonorNames DescentOrdinaryLocalBirth DescentHostDegree DescentHostDirectory DescentOrdinaryDonorHalo
open DescentNetworkPartition Computability.BorderVNP.Crossing DescentSharedCableNames DescentSixParty.StarKeys
open DescentColonies DescentGL DescentWalshTables DescentPacking
open DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage DescentSortedHaloRaster DescentHaloWalkRAM DescentSIMDLookup
open DescentScalarVenueMask DescentHostDirectory.SiteDecode DescentOrdinaryLocalBirth DescentSharedCableNames DescentPackedActorMask
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentScalarBookReshape
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W)
local notation "r" => BitDescription.scannedRows he T
local notation "capV" => Fin (S.groupCount i)×cap.V
local notation "sw" => branchWidth G (fun _ : (r).pairs=>T.z) ((r).profile c)
local notation "stepGraph" => rawGraph he T c
local notation "sel" => scanWorld he T c
local notation "next" => (ticket.advance arch).bit
local notation "units" => fun _ : (r).pairs=>T.z
local notation "stageLimit" => fun _ : (r).pairs=>le_refl T.z
local notation "layout" => bestLayout sw
local notation "group" => GadgetNetwork.newSite W.graph (r).pick layout (r).pack

local notation "bookChart" => activeChart ticket
local notation "key" => (bookChart).key he T c
local notation "addr" => MarkedWorld.address sel key (bookChart).hub T.k (gainExponent 20 T.Δ)
local notation "C" => ↥(MarkedWorld.reclaimed sel key (bookChart).hub T.k (gainExponent 20 T.Δ))
local notation "venue" => addr ∘ group
local notation "base" => physicalBits G W.toWorld (r).pick units stageLimit ((r).profile c) arch.bit.recipe

local notation "A" => cap.placement
local notation "deg" => (A).degree
local notation "near" => groupedNear (A).near
local notation "bound" => (deg+1)^4*2^k
local notation "sites" => (A).site cap.vertex cap.valid.coordinates

local notation "roster" => hostRotor cap.vertex (hostRoster A (cap.vertex.trans Fin.valEmbedding))
local notation "reach" => Gather.reaching roster
local notation "halo" => reachedHalo ticket
local notation "name" => rackName (cap:=cap)

local notation "shelf"=>2^(packExponent 20 deg)+2
local notation "pitch"=>(2^(k+1)-1)*shelf
local notation "raw"=>2^(k+1)*shelf
local notation "used"=>fun p:(r).pairs=>(r).picked (p,0)
local notation "oldID"=>cap.order.trans Fin.valEmbedding
local notation "origin"=>outgoingSlot A oldID S cap.valid (r).pick used
local notation "P"=>DescentHaloWalkRAM.breadth deg
local notation "K"=>1+(A).cap*6
local notation "moves"=>rotor A (groupRank Fin.valEmbedding (cap.vertex.trans Fin.valEmbedding))

open DescentPaidResidentCount DescentActorRaster DescentPackedColony DescentPackedExchange
variable {mb : ℕ}
variable (tokens : DescentColonies.Block k→Fin (1+cap.placement.cap*6)→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→
  DescentScalarVenueMask.Ticket (DescentHaloWalkRAM.breadth cap.placement.degree) (2^(k+1)*(2^(packExponent 20 cap.placement.degree)+2)))
local notation "physical" => DescentScalarVenueMask.fields reach tokens (flags (cap:=cap)) k (gainExponent 20 deg) shelf pitch
local notation "stock" => Descriptors shelf k (A).pos (A).block (ticketParent (he:=he) (T:=T)) (ticketSlot (c:=c) ticket)
  (key∘group) cap.vertex (Function.Embedding.refl _) moves tokens
local notation "oldCensus" => fun x h g=>Census.count A (Equiv.refl _) cap.vertex mb h g x
local notation "counts" => DescentOrdinaryAtomFieldRAM.RoleCounts.priorValue reach oldCensus
local notation "cost" => fun u : W.graph.Site=>((A).records u).length
local notation "dest" => n.destination∘rawInput he T c ((r).state c)

local notation "OH" => Fintype.card cap.V
local notation "OG" => S.groupCount i

open DescentPackedZip ThreeFlat.RAM
open DescentOrdinaryAtomFieldRAM DescentOrdinaryRasterReturn DescentHaloWalkRAM
variable (oldH oldGrain grain start w venueFloor ingressRoof : ℕ) (wide : Fintype.card cap.V≤oldH) (op : Dated.Operands)
    (port : DescentPackedColony.Ports (DescentHaloWalkRAM.breadth cap.placement.degree)) (field : Bank)
    (full : DescentColonies.Block k→Fin (1+cap.placement.cap*6)→Fin oldH→Fin (S.groupCount i)→
      DescentScalarVenueMask.Ticket (DescentHaloWalkRAM.breadth cap.placement.degree) (2^(k+1)*(2^(packExponent 20 cap.placement.degree)+2)))
    (active : Fin oldH→Fin (S.groupCount i)→Cell 1)
local notation "lifted" => cap.vertex.trans (Fin.castLEEmb wide)
local notation "padded" => Gather.reaching (hostRotor lifted (hostRoster A (cap.vertex.trans Fin.valEmbedding)))
local notation "labels" => fun l : Fin pitch=>Packed.token (some l)
local notation "tagBits" => Packed.bits pitch
local notation "rows" => oldH*chunks OG grain
local notation "L" => RoleCounts.Repitch.count oldH OG oldGrain grain k P mb start
local notation "C₀" => (L).roof
local notation "roof₀" => Sweep.HeldRepacked.roof start oldH OG oldGrain grain k P (A).cap mb tagBits pitch
local notation "pb" => Sweep.paidBank C₀ pitch bound (A).cap mb tagBits oldH OG grain
local notation "ab" => Sweep.aliveBank C₀ pitch bound (A).cap mb tagBits oldH OG grain
local notation "code" => Sweep.HeldRepacked.program start oldH OG oldGrain grain k P (A).cap mb tagBits pitch field port op.atoms labels w
local notation "time₀" => Sweep.HeldRepacked.ticks start oldH OG oldGrain grain k P (A).cap mb tagBits pitch field port op.atoms labels w
local notation "out" => Sweep.HeldRepacked.image start oldH OG oldGrain grain k P (A).cap mb tagBits pitch field port op.atoms labels

variable {R afterPitch wirePitch nextPitch:ℕ}(targetFit:Fintype.card target.V≤R)
    (peerBase:ℕ)(priorCount:Bank)(wire_:ℕ→ℕ→Bank)
local notation "NG" => S.groupCount (i+1)
local notation "names" => target.vertex.trans (Fin.castLEEmb targetFit)
local notation "Dnew" => target.placement.degree
local notation "hp" => (⟨priorCount,op.roster,op.hubs⟩:DescentOrdinaryVenueReturn.Sources)
local notation "header" => DescentOrdinaryVenueReturn.phase hp peerBase k oldH D R D' w
local notation "pe" => DescentOrdinaryPeerRows.peers peerBase oldH D R D'
local notation "hu" => DescentOrdinaryVenueReturn.hubs peerBase oldH D R D'
local notation "counter" => DescentOrdinaryPeerCount.newCount peerBase oldH D R D'
local notation "d₀" => (⟨pitch,oldH,R,NG,2^k,mb,grain,afterPitch⟩:DescentVenueQuantityPlanes.Dims)
local notation "raster" => (⟨pb,ab,counter⟩:DescentOrdinaryRasterReturn.Sources)
local notation "γ" => DescentOrdinaryRasterReturn.phase d₀ raster roof₀ w
local notation "issued₀" => DescentOrdinaryRasterReturn.roof d₀ roof₀
local notation "banks" => (⟨pe,hu,DescentOrdinaryRasterReturn.actorBank d₀ roof₀,
  DescentOrdinaryRasterReturn.paidBank d₀ roof₀,wire_⟩:StageVenueTail.Sources)
local notation "date" => (⟨k,R,NG,D',target.placement.cap,mb,afterPitch,wirePitch,afterPitch,nextPitch⟩:StageVenueTail.Date)
local notation "after_" m => (γ).image (out m)
local notation "returned" m => ((date).phase banks issued₀ w).image (after_ m)

/-- The original three physical stages agree on every reached actor, funded row,
signed entry, and the original sorted neighbor raster. The input for the held sweep
is the actual earlier matcher venue field. -/
theorem recorded_ordinary_venue (age:i<S.length)(radix:S.radix=2^k)(old pre wired now:Memory w)
    (stage:stageVenue cap wide op oldGrain mb venueFloor (cap.venueRoster wide) old)
    (rawRows:Reads field (fun h g=>encode tagBits (actors bound (A).cap)
      (DescentScalarVenueMask.fields padded full active k (gainExponent 20 deg) shelf pitch h g)) grain pre)
    (visible:Accessible port field oldH OG grain w ingressRoof)
    (mounted:Mounted port (DescentSortedRoster.indexed padded) pre OG grain)
    (real:∀x j h g,full x j (Fin.castLEEmb wide h) g=tokens x j h g)
    (blank:∀x j (h:Fin oldH) g,OH≤h.val→full x j h g=none)
    (flagsAgree:∀h g,active (Fin.castLEEmb wide h) g=flags (cap:=cap) h g)
    (auth:stock)(precision:(A).wire*((A).z*G.b)*(A).cap<2^mb)
    (positive:0<oldGrain)(beforePeer:venueFloor≤peerBase)(beforeSweep:peerBase ≤ start)
    (didRoute:ingressRoof ≤ start)(oldWords:∀a<venueFloor,now a=old a)
    (saved:∀q< ingressRoof,now q=pre q)(bounds:roof₀<2^w)
    (priorRead:old priorCount.base=(OH:Computability.VPVNP.BurstRAM.Word w))(headerRoom:DescentOrdinaryVenueReturn.Room hp peerBase oldH D R D' w)
    (headerEnd:DescentOrdinaryVenueReturn.roof peerBase oldH D R D' ≤ start)
    (headerFrame:∀j,j<DescentOrdinaryVenueReturn.roof peerBase oldH D R D'→now j=(header).image old j)
    (wireCut:ℕ)(wireCutEarly:wireCut ≤ start)(wireFrame:∀j,j<wireCut→now j=wired j)
    (peerFence:(pe).base+R*D'≤DescentOrdinaryVenueReturn.roof peerBase oldH D R D')
    (hubFence:(hu).base+R≤DescentOrdinaryVenueReturn.roof peerBase oldH D R D')
    (countFence:(counter).base<DescentOrdinaryVenueReturn.roof peerBase oldH D R D')
    (wireFence:∀(x:DescentColonies.Block k)(j:Fin (2*target.placement.cap)),(wire_ x.val j.val).base+R*chunks NG wirePitch≤wireCut)
    (wires:∀(x:DescentColonies.Block k)(j:Fin (2*target.placement.cap)),Reads (wire_ x.val j.val)
      (fun h g=>DescentSignedCableCodec.encode (Prepare.signed target.placement (target.order.trans Fin.valEmbedding)
        S target.valid (Function.Embedding.refl _) names x j h g)) wirePitch wired)
    (m₀:0<grain)(m₁:0<afterPitch)(ms:0<wirePitch)(hosts:0<R)(chunksPos:0<chunks NG afterPitch)
    (space:DescentOrdinaryRasterReturn.Room d₀ raster roof₀ (Fintype.card target.V) w)
    (ready:(date).Space banks issued₀ w):
    stageVenue target targetFit ((date).operands banks issued₀) nextPitch mb ((date).endAddress issued₀)
      (target.venueRoster targetFit) (returned now) ∧
    StageVenueTail.paidCounts banks target targetFit mb afterPitch (after_ now) ∧
    StageVenueTail.paidCounts banks target targetFit mb afterPitch (returned now):=by
  obtain ⟨_,_,frame,allPaid,allSeen⟩:=paid_return_from_venue (mb:=mb) ticket tokens oldH oldGrain grain start w
    venueFloor ingressRoof wide op port field full active old pre now (cap.venueRoster wide) stage rawRows visible mounted real blank
    flagsAgree positive (beforePeer.trans beforeSweep) oldWords didRoute saved bounds
  obtain ⟨_,peers,hub,count,_⟩:=ticket.return_header wide targetFit op priorCount peerBase old stage beforePeer priorRead headerRoom
  have steps:=RoleCounts.Repitch.intervals oldH OG oldGrain grain k P mb start
  have sourceLe:start≤C₀:=steps.1.trans steps.2
  have geom:=Sweep.geometry C₀ pitch bound (A).cap mb tagBits oldH OG grain
  have endPaid:(pb).base+pitch*rows≤roof₀:=geom.2.2.1.trans (geom.2.2.2.1.trans ((Nat.le_add_right ..).trans geom.2.2.2.2))
  have startLe:start≤roof₀:=sourceLe.trans (geom.1.trans (geom.2.1.trans ((Nat.le_add_right ..).trans endPaid)))
  have countPos:=countFence.trans_le headerEnd
  have current:(out now) (counter).base=(Fintype.card target.V:Computability.VPVNP.BurstRAM.Word w):=
    (frame _ (.inl countPos)).trans ((headerFrame _ countFence).trans count)
  have values:=raster_sources (mb:=mb) ticket tokens age radix targetFit wide raster roof₀ (out now)
    auth precision m₀ m₁ hosts chunksPos allPaid allSeen current (countPos.trans_le startLe) endPaid geom.2.2.2.2 space
  have lower (address:ℕ)(lo:address<start):(after_ now) address=now address:=
    ((DescentOrdinaryRasterReturn.any d₀ raster roof₀ (out now) space).2 address (.inl (lo.trans_le startLe))).trans (frame address (.inl lo))
  refine ⟨?_,values.1,(date).paid_counts_after banks target targetFit rfl issued₀ (after_ now) ready values.1⟩
  apply (date).phase_source banks target targetFit issued₀ (after_ now) rfl rfl m₁ ms m₁ (target.venueRoster targetFit) ready
  · intro h j
    have size:h.val*D'+j.val<R*D':=by
      have ij:=(finProdFinEquiv (h,j)).isLt
      simpa only [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm] using ij
    have prior:(pe).base+(h.val*D'+j.val)<DescentOrdinaryVenueReturn.roof peerBase oldH D R D':=
      (Nat.add_lt_add_left size _).trans_le peerFence
    exact (lower _ (prior.trans_le headerEnd)).trans ((headerFrame _ prior).trans (peers h j))
  · intro h
    have prior:(hu).base+h.val<DescentOrdinaryVenueReturn.roof peerBase oldH D R D':=(Nat.add_lt_add_left h.isLt _).trans_le hubFence
    exact (lower _ (prior.trans_le headerEnd)).trans ((headerFrame _ prior).trans (hub h))
  · exact values.2
  · exact values.1
  · intro x j rowId
    have lo:=(Nat.add_lt_add_left (row R NG wirePitch rowId).isLt (wire_ x.val j.val).base).trans_le (wireFence x j)
    exact (lower _ (lo.trans_le wireCutEarly)).trans ((wireFrame _ lo).trans (wires x j rowId))

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
