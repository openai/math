import OAI.Hierarchy.DescentTerminalExecUnique
import OAI.Hierarchy.DescentNamedRetainedMovement
import OAI.Hierarchy.DescentNamedEarlierPlacement
import OAI.Hierarchy.DescentNamedPacketRankEntry

namespace OAI
/-! Both original movement panels and their seven-field payloads follow from the preceding venue and its archive. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentActorRaster DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
variable {F X : Type} [Field F] {d : ℕ} {abits : X→ℕ} {W : MarkedWorld F d X abits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {B : ClosedReset input ctl} (accepted : B.Recorded p)
local notation "board" => ctl.board
local notation "packet" => ctl.bitsR
variable (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
  (venue : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "v" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤laneBits (S.groupWidth k tail age+k) payload (S.localWalshBits p (S.groupWidth k tail age+k) f (quota S.rounds))-k) (fitsSigned : e≤previous) (fitsCut : previous≤S.groupWidth k tail age) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "P" => (a).stencilPhase sh start count io.hubs g (2^n)
local notation "E" => (a).estimator start
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool)
set_option hygiene false

local notation "u" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx
local notation "rawId" => (Z).rawHostRank T rank
local notation "HH" => S.hostSize age
local notation "nBits" => k+S.localWalshBits p (cc+k) f (quota S.rounds)+2
local notation "tBits" => 2*k+n+2
local notation "amp" => input.placement.wire*(input.placement.z*G.b)*input.placement.cap

open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage
local notation "priorCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal io.wire io.roster v
local notation "sourceRows" => DescentResetCanvasIngress.datedLayout input HH (v).funded.oldLanes
  (priorCPU).lanes (priorCPU).short (v).funded.precision (priorCPU).bits
local notation "oldCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal
  ((sourceRows).tokenAt floor) io.roster v
local notation "geom₀" => (a).chart start
local notation "fresh" => (geom₀).remixEnd (a).payload (a).gain (a).positive
local notation "phys₀" => DescentGLPacked.BankImage.Dated.chart (E).endAddress (geom₀).routedHosts (a).high (a).low (a).bits
local notation "saved" => fresh+(2^(E).dim)^(E).dim+(2^(E).dim)^(E).dim
local notation "chip" => ((phys₀).chosen (E).dim).bank (DescentGLNielsen.schedule (E).dim).length
local notation "digits" => S.resetInputDigits ctl.base ctl.radix age
local notation "peer₀" => PackedFlow.portAt input.placement (input.placement.numberedHeader digits input.vertex).site

local notation "res" => (Z).k-(T).commonDepth
local notation "rows" => (roster (Z).graph res (GroupStage.depthBound D n f g)).card
local notation "prev" => fun v=>(Z).placement.b (B.frame.host v)
local notation "U" => (v).actor
local notation "dir" => (U).directory actorBase
local notation "scene" => (U).scene actorBase
local notation "pub" => (((rc).preparedRoots book prepared).seq ((U).classifier (u).actor actorBase w)).seq ((dir).program w scene)
local notation "ticks" => ((rc).preparedTicks book prepared+(U).classifierTime (u).actor actorBase w)+(dir).ticks scene

local notation "entry₀" => (a).ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)

open DescentSortedRoster
local notation "imageOf" degreeAt:arg capAt:arg => fromNamed_root_image (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation "heldRoot" degreeAt:arg capAt:arg measured:arg =>
  (∃hdr : DescentPaidResidentCount.Reset.OriginalHeader B input.valid.host (imageOf degreeAt capAt).receiver
        (imageOf degreeAt capAt).book measured,
    ∃x : DescentPaidResidentCount.Reset.OriginalArrays B input.valid.host (v).middle.rootField,
      ClosedReset.Window.RootPacket B (imageOf degreeAt capAt).receiver (imageOf degreeAt capAt).book
        (imageOf degreeAt capAt).prepared measured hdr (imageOf degreeAt capAt).sources x nBits tBits)
open DescentSixParty.ClosedReset.Window DescentOperandRootPull DescentSixParty.PackedFlow.Channels
local notation "setup" => (v).setup
local notation "r" => (setup).retained
local notation "at_" => (v).operandFloor base₀
local notation "M₁" => 2^e
local notation "coarse" => (T).commonDepth
local notation "span" => (Z).k-coarse
local notation "field" => (v).middle.rootField
local notation "A₁" => input.placement
local notation "rn₁" => (calendar_residual B).symm
local notation "half₁" => (show (a).c/2=cap by change (2*cap)/2=cap;omega)
local notation "Ksig" => Fin (setup).strip→Fin (setup).placement.oldHosts→Fin ((setup).placement.groups*(setup).placement.blocks)→Cell (setup).signedBits


set_option hygiene true
set_option maxHeartbeats 1500000

include accepted in
theorem DateInputs.fromNamed_venue_moved
    (prepared : (rc).PreparedFits book) (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (degreeAt : venue.degree=D) (ready : (u).Ready) (mem : Memory w)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (capAt : input.placement.cap=cap) (history : hist=S.firstWidth G.b p) (branch : G.b≤2^S.capGain)
    (seen : stageVenue input input.valid.host io (v).funded.oldLanes (v).funded.precision floor
      (input.venueRoster input.valid.host) mem) (popFit : count.Fits w floor)
    (popRead : mem count.base=(Fintype.card input.V:Word w))
    (wireRoom : ∀(x:DescentColonies.Block k)(j:Fin (2*input.placement.cap)),(io.wire x.val j.val).Fits w floor ∧
      HH*chunks (S.groupCount age) (v).funded.oldLanes≤(io.wire x.val j.val).size)
    (oldPos : 0<(v).funded.oldLanes) (oldWidth : (v).funded.precision=S.censusBits p)
    (entryFits : start<2^w) (low : k≤(E).low)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (live : 0 < amp) (degreePos : 0 < 32*Nat.clog 2 (2*venue.degree))
    (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p) ≤ w) (hostBits : HH < 2^w)
    (ranksFit : venue.degree*2^Ht < 2^w)
    (namesFit : DescentFallbackShapeTable.actorWordBits k (32*Nat.clog 2 (2*venue.degree)) g n ≤ w)
    (degFit : venue.degree+1 < 2^w) (laneRoom : 2^e ≤ w)
    (oldHubRoom : HH≤ io.hubs.size) (capacity : venue.cap=cap) (pitchOld : venue.lanes=2^previous)
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e) (small : 8*(v).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w)
    (blocksAt : venue.k=k) (oldH : venue.hosts=HH) (priorPos : 0<oldLanes)
    (newFit : S.hostSize (age+1)≤2^w) (old : (r).Values)
    (data : ∀j,((u).bank.old j).Fits w floor ∧ (r).hosts*chunks (r).groups (r).previousLanes≤((u).bank.old j).size ∧
      Reads ((u).bank.old j) (old j) (r).previousLanes mem) :
    let im:=imageOf degreeAt capAt
    let donor:=(u).menu.donors.trans (congrArg (2^·) rn₁)
    let bound:=(u).menu.capacity.trans ((half₁).trans capAt.symm)
    let which:=fun j:Fin (setup).strip=>(finProdFinEquiv (m:=(r).donors) (n:=2*(setup).oldCap)).symm j
    ∃(μ : DescentGL.Layout (E).dim) (measured actors : Memory w)
      (hdr : DescentPaidResidentCount.Reset.OriginalHeader B input.valid.host im.receiver im.book measured)
      (x : DescentPaidResidentCount.Reset.OriginalArrays B input.valid.host field) (X : (setup).seven.Packets) (sig : Ksig)
      (geo : (setup).MovementShape) (dim : (E).dim=(r).high+(r).low) (size : HH*rows=(setup).placement.sparse),
      let name:=fun j : Fin (Fintype.card B.next.V)=>((Z).rawAtIndex T rank j).cast size
      let strips:=fun j=>blockValues geo.cut ((r).before geo.size old j) (cast (congrArg DescentGL.Layout dim) μ)
      let inputMem:=(u).beforeSetupImage ready actors
      HEq μ B.frame.basis ∧ RootPacket B im.receiver im.book im.prepared measured hdr im.sources x nBits tBits ∧
      ((a).throughStencil sh start count io.hubs g (2^n) ((a).ingress.source floor)
        (S.groupCount age) venue.degree w).Exec ((entry₀).image mem) measured
          ((a).throughStencilTicks sh start count io.hubs g (2^n) (S.groupCount age) venue.degree w) ∧
      (pub).Exec measured actors ticks ∧
      (setup).Moved at_ (u).bank name (((setup).sources at_ w (u).bank).image inputMem)
        ((setup).assignedDigits geo.host geo.groups (u).bank.which X strips) sig ∧
      (∀host hi, (X host hi).val=(encode field (DescentRotorWindowArchive.count (A₁).degree (2^span) (A₁).cap)
        (calendar_sender_matrix B M₁ field im.receiver im.book im.prepared measured hdr x host ⟨hi.val,by rw [B.commonDepth];exact hi.isLt⟩)).val) ∧
      (∀j host hi, (sig j host hi).val =
        (((DescentSignedCableCodec.encode (originalCable B x host
          ⟨hi.val,by rw [B.commonDepth,S.group_cut B.age,pow_add,S.group_power ctl.base ctl.radix];exact hi.isLt⟩
          ((which j).1.cast donor) ((which j).2.cast (congrArg (2*·) bound)))).val:Cell field)).val) :=by
  dsimp only
  obtain ⟨μ,measured,actors,won,savedWord,kept,reserved,order,panel,scanned,published,whole,total,inv,fwd,
      flags,lowDst,⟨hdr,x,words⟩,basis,mid,post,agreements,roster,hubs,occupied,rootCount,depths,levels,midHubs,dstHubs⟩:=
    DateInputs.fromNamed_packet_entry (B:=B) accepted drift degree payload e previous M nextM oldLanes
      primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
      initial prepared sceneRoom degreeAt ready mem gr fee capAt history branch seen popFit popRead wireRoom oldPos oldWidth
      entryFits low score live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom oldHubRoom capacity
      pitchOld chosen pitch small word ceiling
  obtain ⟨X,sig,window,port,targets,sockets⟩:=DateInputs.fromNamed_earlier_placement (B:=B) drift degree payload
    e previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
    previousMeta previousArguments initial prepared sceneRoom degreeAt capAt ready chosen pitch small word ceiling
    capacity gr fee measured hdr x words
  subst actors
  obtain ⟨geo,dim,size,moved⟩:=DateInputs.fromNamed_retained_moved (B:=B) drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom ready degreeAt capAt blocksAt oldH (pitch.symm ▸ Nat.two_pow_pos e) priorPos newFit
    μ mem measured mid old X sig data savedWord kept scanned published total inv lowDst rootCount window port
  exact ⟨μ,measured,(dir).result scene mid,hdr,x,X,sig,geo,dim,size,won,words,scanned,published,moved,targets,sockets⟩

/-- The earlier archive and signed matrix on a specified acquired actor memory. -/
def DateInputs.MovementAt
    (prepared : (rc).PreparedFits book)
  (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)
    (ready : (u).Ready) (old : (r).Values) (μ : DescentGL.Layout (E).dim) (measured actors : Memory w) : Prop :=
    let im:=imageOf degreeAt capAt
    let donor:=(u).menu.donors.trans (congrArg (2^·) rn₁)
    let bound:=(u).menu.capacity.trans ((half₁).trans capAt.symm)
    let which:=fun j:Fin (setup).strip=>(finProdFinEquiv (m:=(r).donors) (n:=2*(setup).oldCap)).symm j
    ∃(hdr : DescentPaidResidentCount.Reset.OriginalHeader B input.valid.host im.receiver im.book measured)
      (x : DescentPaidResidentCount.Reset.OriginalArrays B input.valid.host field) (X : (setup).seven.Packets) (sig : Ksig)
      (geo : (setup).MovementShape) (dim : (E).dim=(r).high+(r).low) (size : HH*rows=(setup).placement.sparse),
      let name:=fun j : Fin (Fintype.card B.next.V)=>((Z).rawAtIndex T rank j).cast size
      let strips:=fun j=>blockValues geo.cut ((r).before geo.size old j) (cast (congrArg DescentGL.Layout dim) μ)
      let inputMem:=(u).beforeSetupImage ready actors
      RootPacket B im.receiver im.book im.prepared measured hdr im.sources x nBits tBits ∧
      (setup).Moved at_ (u).bank name (((setup).sources at_ w (u).bank).image inputMem)
        ((setup).assignedDigits geo.host geo.groups (u).bank.which X strips) sig ∧
      (∀host hi, (X host hi).val=(encode field (DescentRotorWindowArchive.count (A₁).degree (2^span) (A₁).cap)
        (calendar_sender_matrix B M₁ field im.receiver im.book im.prepared measured hdr x host ⟨hi.val,by rw [B.commonDepth];exact hi.isLt⟩)).val) ∧
      (∀j host hi, (sig j host hi).val =
        (((DescentSignedCableCodec.encode (originalCable B x host
          ⟨hi.val,by rw [B.commonDepth,S.group_cut B.age,pow_add,S.group_power ctl.base ctl.radix];exact hi.isLt⟩
          ((which j).1.cast donor) ((which j).2.cast (congrArg (2*·) bound)))).val:Cell field)).val)

include accepted in
theorem DateInputs.fromNamed_movement_at
    (prepared : (rc).PreparedFits book) (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (degreeAt : venue.degree=D) (ready : (u).Ready) (mem : Memory w)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (capAt : input.placement.cap=cap) (history : hist=S.firstWidth G.b p) (branch : G.b≤2^S.capGain)
    (seen : stageVenue input input.valid.host io (v).funded.oldLanes (v).funded.precision floor
      (input.venueRoster input.valid.host) mem) (popFit : count.Fits w floor)
    (popRead : mem count.base=(Fintype.card input.V:Word w))
    (wireRoom : ∀(x:DescentColonies.Block k)(j:Fin (2*input.placement.cap)),(io.wire x.val j.val).Fits w floor ∧
      HH*chunks (S.groupCount age) (v).funded.oldLanes≤(io.wire x.val j.val).size)
    (oldPos : 0<(v).funded.oldLanes) (oldWidth : (v).funded.precision=S.censusBits p)
    (entryFits : start<2^w) (low : k≤(E).low)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (live : 0 < amp) (degreePos : 0 < 32*Nat.clog 2 (2*venue.degree))
    (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p) ≤ w) (hostBits : HH < 2^w)
    (ranksFit : venue.degree*2^Ht < 2^w)
    (namesFit : DescentFallbackShapeTable.actorWordBits k (32*Nat.clog 2 (2*venue.degree)) g n ≤ w)
    (degFit : venue.degree+1 < 2^w) (laneRoom : 2^e ≤ w)
    (oldHubRoom : HH≤ io.hubs.size) (capacity : venue.cap=cap) (pitchOld : venue.lanes=2^previous)
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e) (small : 8*(v).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w)
    (blocksAt : venue.k=k) (oldH : venue.hosts=HH) (priorPos : 0<oldLanes)
    (newFit : S.hostSize (age+1)≤2^w) (old : (r).Values)
    (data : ∀j,((u).bank.old j).Fits w floor ∧ (r).hosts*chunks (r).groups (r).previousLanes≤((u).bank.old j).size ∧
      Reads ((u).bank.old j) (old j) (r).previousLanes mem)

    (μ : DescentGL.Layout (E).dim) (measured actors : Memory w) (basis : HEq μ B.frame.basis)
    (scan : ((a).throughStencil sh start count io.hubs g (2^n) ((a).ingress.source floor)
        (S.groupCount age) venue.degree w).Exec ((entry₀).image mem) measured
          ((a).throughStencilTicks sh start count io.hubs g (2^n) (S.groupCount age) venue.degree w))
    (posted : (pub).Exec measured actors ticks) :
    DateInputs.MovementAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
      venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
      degreeAt capAt ready old μ measured actors:=by
  obtain ⟨basis',measured',actors',hdr,xs,X,sig,geo,dim,size,won,root,scanned,published,moved,windows,signed⟩:=
    DateInputs.fromNamed_venue_moved (B:=B) accepted drift degree payload e previous M nextM oldLanes
      primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
      initial prepared sceneRoom degreeAt ready mem gr fee capAt history branch seen popFit popRead wireRoom oldPos
      oldWidth entryFits low score live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom oldHubRoom
      capacity pitchOld chosen pitch small word ceiling blocksAt oldH priorPos newFit old data
  have hμ : basis'=μ:=eq_of_heq (won.trans basis.symm)
  have m₁ : measured'=measured:=ProtocolRAM.exec_unique _ _ _ _ scanned scan
  subst basis'
  subst measured'
  have m₂ : actors'=actors:=ProtocolRAM.exec_unique _ _ _ _ published posted
  subst actors'
  exact ⟨hdr,xs,X,sig,geo,dim,size,root,moved,windows,signed⟩


end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
