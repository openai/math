import OAI.Hierarchy.DescentDatedOrdinaryVenueModel

namespace OAI
/-! # The returned ordinary placement on its dated, printed and clipped original memory -/
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
variable {F Pin:Type} [Field F](v:Chronology.PhysicalOrdinary F Pin)(floor:ℕ)
local notation "S" => v.schedule
local notation "k" => v.k
local notation "i" => v.age
local notation "G" => v.gadget
local notation "W" => v.world
local notation "cap" => v.prior
local notation "target" => v.target
local notation "ticket" => v.ticket
local notation "he" => v.nonnegative
local notation "T" => v.stage
local notation "c" => v.choice
local notation "n" => v.normalize
local notation "D" => v.degree
local notation "D'" => v.nextDegree
local notation "mb" => v.venue.paidBits
local notation "oldH" => v.area.H
local notation "R" => v.venue.hosts
local notation "oldGrain" => v.area.lanesAt
local notation "grain" => v.rasterLanes
local notation "afterPitch" => v.venue.paidLanes
local notation "wirePitch" => v.venue.signedLanes
local notation "nextPitch" => v.venue.lanes
local notation "peerBase" => v.materialEnd floor
local notation "start" => v.endAddress floor
local notation "wire_" => v.reachedWire floor
local notation "r" => BitDescription.scannedRows he T
local notation "sw" => branchWidth G (fun _ : (r).pairs=>(T).z) ((r).profile c)
local notation "layout" => bestLayout sw
local notation "group" => GadgetNetwork.newSite (W).graph (r).pick layout (r).pack
local notation "bookChart" => activeChart ticket
local notation "key" => (bookChart).key he T c
local notation "A" => (cap).placement
local notation "deg" => (A).degree
local notation "roster" => hostRotor (cap).vertex (hostRoster A ((cap).vertex.trans Fin.valEmbedding))
local notation "reach" => Gather.reaching roster
local notation "shelf"=>2^(packExponent 20 deg)+2
local notation "pitch"=>(2^(k+1)-1)*shelf
local notation "raw"=>2^(k+1)*shelf
local notation "P"=>DescentHaloWalkRAM.breadth deg
local notation "K"=>1+(A).cap*6
local notation "moves"=>rotor A (groupRank Fin.valEmbedding ((cap).vertex.trans Fin.valEmbedding))
local notation "OH" => Fintype.card (cap).V
local notation "OG" => (S).groupCount i
local notation "NG" => (S).groupCount (i+1)
open DescentPaidResidentCount DescentActorRaster DescentPackedColony DescentPackedExchange
open DescentPackedZip ThreeFlat.RAM DescentOrdinaryAtomFieldRAM DescentOrdinaryRasterReturn
variable {w:ℕ}(venueFloor ingressRoof:ℕ)(wide:(Fintype.card ((v.prior)).V)≤(v.area.H))(targetFit:Fintype.card ((v.target)).V≤(v.venue.hosts))
  (input:Dated.Operands)(shelf_:v.FundedInputs)(priorCount:Bank)
  (tokens : DescentColonies.Block (v.k)→Fin (1+((((v.prior)).placement)).cap*6)→Fin (Fintype.card ((v.prior)).V)→Fin (((v.schedule)).groupCount (v.age))→DescentScalarVenueMask.Ticket (DescentHaloWalkRAM.breadth (((((v.prior)).placement)).degree)) (2^((v.k)+1)*(2^(packExponent 20 (((((v.prior)).placement)).degree))+2)))
  (full : DescentColonies.Block (v.k)→Fin (1+((((v.prior)).placement)).cap*6)→Fin (v.area.H)→Fin (((v.schedule)).groupCount (v.age))→DescentScalarVenueMask.Ticket (DescentHaloWalkRAM.breadth (((((v.prior)).placement)).degree)) (2^((v.k)+1)*(2^(packExponent 20 (((((v.prior)).placement)).degree))+2)))(active:Fin (v.area.H)→Fin (((v.schedule)).groupCount (v.age))→Cell 1)
local notation "op" => input
local notation "field" => shelf_.field
local notation "port" => shelf_.ports
local notation "bound" => (deg+1)^4*2^k
local notation "stock" => Descriptors shelf k (A).pos (A).block (ticketParent («he»:=he) («T»:=T)) (ticketSlot («c»:=c) ticket)
  (key∘group) (cap).vertex (Function.Embedding.refl _) moves tokens
local notation "lifted" => (cap).vertex.trans (Fin.castLEEmb wide)
local notation "padded" => Gather.reaching (hostRotor lifted (hostRoster A ((cap).vertex.trans Fin.valEmbedding)))
local notation "tagBits" => Packed.bits pitch
local notation "L" => RoleCounts.Repitch.count oldH OG oldGrain grain k P mb start
local notation "C₀" => (L).roof
local notation "roof₀" => Sweep.HeldRepacked.roof start oldH OG oldGrain grain k P (A).cap mb tagBits pitch
local notation "pb" => Sweep.paidBank C₀ pitch bound (A).cap mb tagBits oldH OG grain
local notation "ab" => Sweep.aliveBank C₀ pitch bound (A).cap mb tagBits oldH OG grain
local notation "names" => (target).vertex.trans (Fin.castLEEmb targetFit)
local notation "hp" => (⟨priorCount,(op).roster,(op).hubs⟩:DescentOrdinaryVenueReturn.Sources)
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
local notation "date" => (⟨k,R,NG,D',(target).placement.cap,mb,afterPitch,wirePitch,afterPitch,nextPitch⟩:StageVenueTail.Date)
local notation "existing" => v.reachedSources floor
local notation "selected" => v.venue
local notation "begin_" => v.rasterEnd floor
local notation "truePhase" => (selected).phase existing begin_ w
theorem reached_ordinary_venue (blocks:(selected).k=k)(groups:(selected).groups=NG)(degree:(selected).degree=D')
    (capMatch:(selected).cap=(target).placement.cap)(paired:(selected).aliveLanes=afterPitch)
    (room:v.FundedRoom floor shelf_ input w)(age:i<(S).length)(radix:(S).radix=2^k)(old pre wired now:Memory w)
    (stage:stageVenue cap wide op oldGrain mb venueFloor ((cap).venueRoster wide) old)
    (rawRows:Reads field (fun h g=>encode tagBits (actors bound (A).cap)
      (DescentScalarVenueMask.fields padded full active k (gainExponent 20 deg) shelf pitch h g)) grain pre)
    (visible:Accessible port field oldH OG grain w ingressRoof)
    (mounted:Mounted port (DescentSortedRoster.indexed padded) pre OG grain)
    (real:∀x j h g,full x j (Fin.castLEEmb wide h) g=tokens x j h g)
    (blank:∀x j (h:Fin oldH) g,OH≤h.val→full x j h g=none)
    (flagsAgree:∀h g,active (Fin.castLEEmb wide h) g=flags («cap»:=cap) h g)
    (auth:stock)(precision:(A).wire*((A).z*(G).b)*(A).cap<2^mb)
    (positive:0<oldGrain)(beforePeer:venueFloor≤peerBase)(beforeSweep:peerBase ≤ start)
    (didRoute:ingressRoof ≤ start)(oldWords:∀a<venueFloor,now a=old a)
    (saved:∀q< ingressRoof,now q=pre q)
    (priorRead:old priorCount.base=(OH:Computability.VPVNP.BurstRAM.Word w))(headerRoom:DescentOrdinaryVenueReturn.Room hp peerBase oldH D R D' w)
    (headerEnd:DescentOrdinaryVenueReturn.roof peerBase oldH D R D' ≤ start)
    (headerFrame:∀j,j<DescentOrdinaryVenueReturn.roof peerBase oldH D R D'→now j=(header).image old j)
    (wireCut:ℕ)(wireCutEarly:wireCut ≤ start)(wireFrame:∀j,j<wireCut→now j=wired j)
    (peerFence:(pe).base+R*D'≤DescentOrdinaryVenueReturn.roof peerBase oldH D R D')
    (hubFence:(hu).base+R≤DescentOrdinaryVenueReturn.roof peerBase oldH D R D')
    (countFence:(counter).base<DescentOrdinaryVenueReturn.roof peerBase oldH D R D')
    (wireFence:∀(x:DescentColonies.Block k)(j:Fin (2*(target).placement.cap)),(wire_ x.val j.val).base+R*chunks NG wirePitch≤wireCut)
    (wires:∀(x:DescentColonies.Block k)(j:Fin (2*(target).placement.cap)),Reads (wire_ x.val j.val)
      (fun h g=>DescentSignedCableCodec.encode (Prepare.signed (target).placement ((target).order.trans Fin.valEmbedding)
        S (target).valid (Function.Embedding.refl _) names x j h g)) wirePitch wired)
    (m₀:0<grain)(m₁:0<afterPitch)(ms:0<wirePitch)(hosts:0<R)(chunksPos:0<chunks NG afterPitch)
    (ready:(selected).Space existing begin_ w):
    stageVenue target targetFit ((selected).operands existing begin_) nextPitch mb ((selected).endAddress begin_)
      ((target).venueRoster targetFit) ((truePhase).image ((v.fundedRaster floor shelf_ op w room).image now)) ∧
    StageVenueTail.paidCounts existing target targetFit mb afterPitch ((v.fundedRaster floor shelf_ op w room).image now) ∧
    StageVenueTail.paidCounts existing target targetFit mb afterPitch ((truePhase).image ((v.fundedRaster floor shelf_ op w room).image now)):=by
  have trueDate:(date)=selected:=v.reachedDate blocks groups degree capMatch paired
  have trueDims:(d₀)=StageVenueTail.OrdinaryRaster.dims v.area (selected) grain:=by
    change (⟨pitch,oldH,R,NG,2^k,mb,grain,afterPitch⟩:DescentVenueQuantityPlanes.Dims)=
      ⟨pitch,oldH,R,(selected).groups,2^k,mb,grain,afterPitch⟩
    rw [groups]
  have newPeer : (pe)=DescentOrdinaryPeerRows.peers peerBase oldH v.area.D R (selected).degree:=by
    change _=DescentOrdinaryPeerRows.peers peerBase oldH (cap).placement.degree R (selected).degree
    rw [(cap).branch,degree]
  have newHub : (hu)=DescentOrdinaryVenueReturn.hubs peerBase oldH v.area.D R (selected).degree:=by
    change _=DescentOrdinaryVenueReturn.hubs peerBase oldH (cap).placement.degree R (selected).degree
    rw [(cap).branch,degree]
  have newCount : (counter)=DescentOrdinaryPeerCount.newCount peerBase oldH v.area.D R (selected).degree:=by
    change _=DescentOrdinaryPeerCount.newCount peerBase oldH (cap).placement.degree R (selected).degree
    rw [(cap).branch,degree]
  have lower:(raster)=v.paidRasterBanks floor:=by rw [newCount];rfl
  have sources:(banks)=existing:=by rw [newPeer,newHub,trueDims];rfl
  have position:issued₀=begin_:=by rw [trueDims];rfl
  have space:DescentOrdinaryRasterReturn.Room (StageVenueTail.OrdinaryRaster.dims v.area (selected) grain)
      (v.paidRasterBanks floor) (StageVenueTail.OrdinaryRaster.sweep v.area (selected) grain start)
      (Fintype.card (target).V) w:=
    DescentOrdinaryRasterReturn.Room.observed _ _ _ room.compact.choose_spec targetFit
  have run:=recorded_ordinary_venue («mb»:=mb) ticket tokens oldH oldGrain grain start w venueFloor ingressRoof wide op
    port field full active targetFit peerBase priorCount wire_ age radix old pre wired now stage rawRows visible mounted
    real blank flagsAgree auth precision positive beforePeer beforeSweep didRoute oldWords saved room.roof priorRead headerRoom
    headerEnd headerFrame wireCut wireCutEarly wireFrame peerFence hubFence countFence wireFence wires m₀ m₁ ms hosts chunksPos
    (by rw [trueDims,lower];exact space) (by rw [trueDate,sources,position];exact ready)
  let claim (d : StageVenueTail.Date) (src : StageVenueTail.Sources) (cut : ℕ) (out : Memory w) :=
    stageVenue target targetFit (d.operands src cut) nextPitch mb (d.endAddress cut)
      ((target).venueRoster targetFit) ((d.phase src cut w).image out) ∧
    StageVenueTail.paidCounts src target targetFit mb afterPitch out ∧
    StageVenueTail.paidCounts src target targetFit mb afterPitch ((d.phase src cut w).image out)
  let held := (v.heldPhase floor shelf_ op w room).image now
  have dated : claim (date) (banks) issued₀ ((γ).image held) := run
  have actual : (γ).image held = (v.fundedRaster floor shelf_ op w room).image now := by
    rw [trueDims, lower]
    rfl
  change claim selected existing begin_ ((v.fundedRaster floor shelf_ op w room).image now)
  rw [← trueDate, ← sources, ← position, ← actual]
  exact dated

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
