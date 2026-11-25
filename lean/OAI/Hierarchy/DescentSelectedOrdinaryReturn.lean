import OAI.Hierarchy.DescentDatedRecordedOrdinaryVenue
import OAI.Hierarchy.DescentRegisteredSelectedActors

namespace OAI
/-! # The selected board and its two signed ends give the genuine returned ordinary venue -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentLocalArchiveOrder
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

open DescentOrdinaryVenueIngress
variable {w:ℕ} (wide:Fintype.card v.prior.V≤v.area.H)(targetFit:Fintype.card v.target.V≤v.venue.hosts)
  (input:Dated.Operands)(priorCount parts:Bank)(extra:ℕ)
local notation "lifted" => (cap).vertex.trans (Fin.castLEEmb wide)
local notation "names" => (target).vertex.trans (Fin.castLEEmb targetFit)
local notation "ro" => hostRotor lifted (hostRoster A ((lifted).trans Fin.valEmbedding))
local notation "padded" => Gather.reaching (hostRotor lifted (hostRoster A ((cap).vertex.trans Fin.valEmbedding)))
local notation "clip" => v.fundedClip extra
local notation "beg" => v.signedEnd floor
local notation "end_" => (clip).fullEnd beg
local notation "op" => input
local notation "donorIO" => ingressInputs input parts
local notation "pre" wired => ((clip).phase donorIO beg w).image wired
local notation "money" => (⟨(clip).fieldBank beg,(clip).ports beg⟩:v.FundedInputs)
local notation "hp" => (⟨priorCount,input.roster,input.hubs⟩:DescentOrdinaryVenueReturn.Sources)
local notation "header" => DescentOrdinaryVenueReturn.phase hp peerBase k oldH D R D' w
local notation "pe" => DescentOrdinaryPeerRows.peers peerBase oldH D R D'
local notation "hu" => DescentOrdinaryVenueReturn.hubs peerBase oldH D R D'
local notation "counter" => DescentOrdinaryPeerCount.newCount peerBase oldH D R D'
local notation "selected" => v.venue
local notation "existing" => v.reachedSources floor
local notation "begin_" => v.rasterEnd floor
local notation "truePhase" => (selected).phase existing begin_ w
variable (choice:(v.prior.placement.stage.result v.nonnegative).Choice)(m:Memory w)
  (board_:v.SelectedBoard wide (hostRotor (v.prior.vertex.trans (Fin.castLEEmb wide)) (hostRoster v.prior.placement ((v.prior.vertex.trans (Fin.castLEEmb wide)).trans Fin.valEmbedding))) choice m parts)(sameChoice:HEq choice v.choice)
local notation "mode" => bestLayout (branchWidth G (fun _: (BitDescription.scannedRows he (A).stage).pairs=>(A).stage.z)
  ((BitDescription.scannedRows he (A).stage).profile choice))
local notation "native" => (cap).order.trans Fin.valEmbedding
local notation "rk" => groupRank Fin.valEmbedding ((cap).vertex.trans Fin.valEmbedding)
local notation "tokens₀" => DescentScalarVenueMask.Stage.tokens (short:=v.short) A native S (cap).valid rk
  board_.win v.profile mode (Function.Embedding.refl _) (cap).vertex shelf
local notation "full₀" => DescentScalarVenueMask.Stage.tokens (short:=v.short) A native S (cap).valid
  (groupRank Fin.valEmbedding ((lifted).trans Fin.valEmbedding)) board_.win v.profile mode (Function.Embedding.refl _) lifted shelf

set_option maxHeartbeats 800000 in
include board_ sameChoice in
theorem selected_ordinary_venue (work:grain=(clip).working)
    (blocks:(selected).k=k)(groups:(selected).groups=NG)(degree:(selected).degree=D')
    (capMatch:(selected).cap=(target).placement.cap)(paired:(selected).aliveLanes=afterPitch)
    (room:v.FundedRoom floor money input w)(age:i<(S).length)(radix:(S).radix=2^k)
    (venueFloor:ℕ)(old wired now:Memory w)
    (stage:stageVenue cap wide input oldGrain mb venueFloor ((cap).venueRoster wide) old)
    (lower:∀a<venueFloor,wired a=old a)
    (panel:∀p:Row oldH OG v.withIssuedSigned.material.oldLanes,
       wired (parts.base+(row oldH OG v.withIssuedSigned.material.oldLanes p).val)=
       m (parts.base+(row oldH OG v.withIssuedSigned.material.oldLanes p).val))
    (clipOK:(clip).Room donorIO beg w)(clipEnd:end_<2^w)
    (precision:(A).wire*((A).z*(G).b)*(A).cap<2^mb)
    (positive:0<oldGrain)(beforePeer:venueFloor≤peerBase)(beforeSweep:peerBase≤ start)
    (didRoute:end_≤ start)(oldWords:∀a<venueFloor,now a=old a)(saved:∀a<end_,now a=(pre wired) a)
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
      ((target).venueRoster targetFit) ((truePhase).image ((v.fundedRaster floor money input w room).image now)) ∧
    StageVenueTail.paidCounts existing target targetFit mb afterPitch ((v.fundedRaster floor money input w room).image now) ∧
    StageVenueTail.paidCounts existing target targetFit mb afterPitch ((truePhase).image ((v.fundedRaster floor money input w room).image now)):=by
  have rankEq : (lifted).trans Fin.valEmbedding=(cap).vertex.trans Fin.valEmbedding:=by ext x;rfl
  obtain ⟨read,mounted,access⟩:=v.funded_selected_ingress wide choice m parts board_ input mb venueFloor beg extra
    old wired stage lower panel positive clipOK clipEnd
  obtain ⟨live,blank,flagsAt⟩:=v.selected_token_rows wide choice m parts board_
  apply DescentLocalArchiveOrder.reached_ordinary_venue v floor (venueFloor:=venueFloor) (ingressRoof:=end_) (wide:=wide)
    (targetFit:=targetFit) (input:=input) (shelf_:=money) (priorCount:=priorCount)
    (tokens:=tokens₀) (full:=full₀) (active:=fun h _=>Census.hub A lifted h)
    blocks groups degree capMatch paired room age radix old (pre wired) wired now stage _ _ _ live blank _
    (v.selected_descriptors wide choice m parts board_ sameChoice) precision positive beforePeer beforeSweep
    didRoute oldWords saved priorRead headerRoom headerEnd headerFrame wireCut wireCutEarly wireFrame
    peerFence hubFence countFence wireFence wires m₀ m₁ ms hosts chunksPos ready
  · rw [work]
    simp only [rankEq] at read ⊢
    with_unfolding_all exact read
  · rw [work]
    with_unfolding_all exact access
  · rw [work]
    simp only [rankEq] at mounted ⊢
    with_unfolding_all exact mounted
  · intro h g
    exact (flagsAt h).trans (census_hub_flags («cap»:=cap) h g)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
