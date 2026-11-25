import OAI.Hierarchy.DescentNamedPrimitiveVenue
import OAI.Hierarchy.DescentNamedPacketRankEntry
import OAI.Hierarchy.DescentNamedFundedPacket
import OAI.Hierarchy.DescentRecordedCensusMass

namespace OAI
/-! Primitive venue and compact census from the measured root packet on the original named date. -/

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
  (B : ClosedReset input ctl)
local notation "board" => ctl.board
local notation "packet" => ctl.bitsR
variable (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
  (venue : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "successor₀" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤(laneBits ((S.groupWidth k tail age)+k) payload (S.localWalshBits p ((S.groupWidth k tail age)+k) f (quota S.rounds)))-k) (fitsSigned : e≤previous) (fitsCut : previous≤(S.groupWidth k tail age)) (count : Bank)
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
local notation "actorBase" => (successor₀).middle.stop base₀
local notation "early" => (successor₀).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : ((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rootPhase (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w)).PreparedFits (atlasBook (namedAtlas G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) count) (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w))
  (sceneRoom : ((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).front.SceneRoom (((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).actorEnd (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor))) (((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).issuedScene (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor)) (namedOriginals G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count)) w)
local notation "u" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx
local notation "rawId" => (Z).rawHostRank T rank
local notation "HH" => S.hostSize age
open ClosedReset.Window DescentResetActorClass DescentResetDenseOperand
local notation "D₀" => (successor₀).actor.directory actorBase
local notation "A₀" => (successor₀).actorClass
local notation "L₀" => (successor₀).birth.placement
local notation "K₀" => (successor₀).birth.classBits
local notation "res" => (Z).k-(T).commonDepth
local notation "num" => Fintype.card B.next.V
local notation "earlyName" => originalCompactName B HH input.valid.host
local notation "roleAt" => (successor₀).fullEnd base₀
local notation "movedAt" => (successor₀).roleEnd base₀
local notation "classAt" => (successor₀).classEnd base₀
variable (z₀ : @FinalInputs (named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor) (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) w ((DateInputs.fromNamed G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count) previousMeta previousArguments initial prepared sceneRoom))

local notation "expected" key => (Fin.cast (congrArg (fun b : ℕ=>2^b) (show K₀=indexBits (Z).n res from by
  change indexBits n k=_
  rw [B.dimension,calendar_residual B]).symm)
  ((paidActorAt B key).elim 0 (fun actor=>indexed (Z).graph res actor.val)))

local notation "nBits" => k+S.localWalshBits p (cc+k) f (quota S.rounds)+2
local notation "tBits" => 2*k+n+2
local notation "amp" => input.placement.wire*(input.placement.z*G.b)*input.placement.cap

local notation "entry₀" => (a).ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)


variable (accepted : B.Recorded p)

open DescentPacking.PackedMatch.Local.Stage DescentFundedCensus DescentPaidResidentCount.Reset
open DescentSharedCableNames DescentFallbackPeriod.Projected DescentSixParty.ClosedReset DescentGL DescentIssuedFallbackPanel
open DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage
local notation "st_" => (a).throughStencil (u).shape start (u).count (u).hub (u).g (u).Y
  (u).src (u).sourceRows (u).oldDegree w
local notation "time_" => (a).throughStencilTicks (u).shape start (u).count (u).hub (u).g (u).Y
  (u).sourceRows (u).oldDegree w
local notation "fund_" => (successor₀).funded
local notation "bill_" => (successor₀).venue.census
local notation "precision" => (bill_).bits
local notation "key_" => (⟨(P).saved,0⟩:Bank)
local notation "feeStart" => (successor₀).fundedEnd base₀
local notation "feeBanks" => fundedPorts (funded_residual B) B.dimension z₀.ports
local notation "enter" src => (entry₀).image src

local notation "im" degreeAt:arg capAt:arg => fromNamed_root_image (B:=B) drift degree payload e previous M nextM oldLanes
  primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt

private theorem funded_reindex {H H' field lanes width : ℕ} (pad : Fintype.card input.V≤H)
    (hosts : H=H') (ports : DescentFundedCensus.Ports res (Z).n) (mem : Memory width)
    (snap : PaddedSnapshot B pad field)
    (rd : ∀s t, Source (ports.bank s t) (savedInput B pad snap) lanes mem) :
    ∃snapshot : PaddedSnapshot B (pad.trans_eq hosts) field, ∀s t,
      Source (ports.bank s t) (savedInput B (pad.trans_eq hosts) snapshot) lanes mem:=by
  subst H'
  exact ⟨snap,rd⟩

private theorem panel_reindex {a₁ a₂ H field fees width out lanes : ℕ} (dim : a₁+a₂=cc+k)
    (basis : DescentGL.Layout (a₁+a₂)) (won : HEq basis B.frame.basis) (hosts : HH=H) (mem : Memory width)
    (read : PackedFlow.Padded.Published (h:=cc) (l:=k) lanes field out idx
      (ClosedReset.Recorded.realPanel (reset:=B) rfl B.frame.basis fees field) mem) :
    PackedFlow.Padded.Published (h:=a₁) (l:=a₂) lanes field out
      (input.vertex.trans (Fin.castLEEmb (input.valid.host.trans_eq hosts)))
      (ClosedReset.Recorded.realPanel (reset:=B) dim basis fees field) mem:=by
  subst H
  exact ClosedReset.real_panel_width B dim basis won out mem read

private theorem move_basis {dimA dimB : ℕ} (eqn : dimA=dimB) (basis : DescentGL.Layout dimA) :
    HEq (cast (congrArg DescentGL.Layout eqn) basis) basis ∧
      (DescentExterior.matrixCode (cast (congrArg DescentGL.Layout eqn) basis)).val=
        (DescentExterior.matrixCode basis).val:=by
  cases eqn
  exact ⟨HEq.rfl,rfl⟩

include accepted in
/-- The same physical scan supplies the funded fallback pages and the original stencil at the attained basis. -/
theorem fromNamed_packet_primitive_venue (degreeAt : venue.degree=D) (ready : (u).Ready) (mem : Memory w)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (capAt : input.placement.cap=cap) (history : hist=S.firstWidth G.b p) (branch : G.b≤2^S.capGain)
    (seen : stageVenue input input.valid.host io (successor₀).funded.oldLanes (successor₀).funded.precision floor
      (input.venueRoster input.valid.host) mem) (popFit : count.Fits w floor)
    (popRead : mem count.base=(Fintype.card input.V:Word w))
    (wireRoom : ∀(x:DescentActorRaster.Block k)(j:Fin (2*input.placement.cap)),(io.wire x.val j.val).Fits w floor ∧
      HH*chunks (S.groupCount age) (successor₀).funded.oldLanes≤(io.wire x.val j.val).size)
    (oldPos : 0<(successor₀).funded.oldLanes) (oldWidth : (successor₀).funded.precision=S.censusBits p)
    (entryFits : start<2^w) (low : k≤(E).low)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (grain : 0<p) (degreePos : 0 < 32*Nat.clog 2 (2*venue.degree))
    (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p) ≤ w) (hostBits : HH < 2^w)
    (ranksFit : venue.degree*2^Ht < 2^w)
    (namesFit : DescentFallbackShapeTable.actorWordBits k (32*Nat.clog 2 (2*venue.degree)) g n ≤ w)
    (degFit : venue.degree+1 < 2^w) (laneRoom : 2^e ≤ w)
    (hosts : HH=venue.hosts) (groups : venue.groups=S.groupCount age)
    (blocks : venue.k=k) (capacity : venue.cap=input.placement.cap) (pitch : venue.lanes=2^previous)
    (readLanes : (fund_).oldLanes=venue.lanes) (readBits : (fund_).precision=precision)
    (original : z₀.io=io) (safe : z₀.Room) (banks : IssuedBanks io venue.hosts (S.groupCount age) venue.lanes)
    (oldHub : io.hubs.Fits w floor) (oldAtom : ∀x:Fin (2^(a).ingress.k),(io.atoms x.val).Fits w floor)
    (oldWire : ∀j:(a).ingress.signed.Slot,(io.wire j.1.val j.2.val).Fits w floor)
    (oldHubRoom : HH≤ io.hubs.size)
    (cutAt : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (rootLanes : M=2^e)
    (small : 8*(successor₀).groupWidth≤payload) (word : payload≤w) (ceiling : (a).fullEnd floor<2^w)
    (newHost:0<S.hostSize (age+1))(newChunks:0<chunks (S.groupCount (age+1)) M)
    {snapshot:Memory w} (atOperands:(u).throughOperandDate.Runs (enter mem) snapshot) :
    (successor₀).metadata.chart.blocks≤2^(successor₀).venue.next.k ∧
    0<(successor₀).birth.sourceLanes ∧
    z₀.venueImage snapshot (D₀).count.base=(num:Word w) ∧
    (∀j:Fin num,z₀.venueImage snapshot ((D₀).inverse.base+j.val)=((earlyName j).val:Word w)) ∧
    num<2^w ∧ (L₀).newHosts≤2^w ∧ num≤(D₀).inverse.size ∧
    (∀site,(B.next.placement.records site).length<2^(successor₀).birth.paidBits) ∧
    Source (FinalInputs.classWord u) (fun (h:Fin (L₀).newHosts) (_:Fin (L₀).groups)=>expected h)
      (L₀).lanes (z₀.classImage snapshot) ∧
    ∀x:DescentActorRaster.Block k,Source (.lookup (((successor₀).venue.sources (FinalInputs.predecessor u) feeStart).paid x.val) .row)
        (fun h g=>Census.count B.next.placement (Equiv.refl _) (B.next.vertex.trans (Fin.castLEEmb B.next.valid.host))
          venue.paidBits h g x) M (z₀.venueImage snapshot):=by
  have census:=posted_census_limits B p grain gr fee branch capAt
  have caps:=posted_actor_packet_limits B p gr fee branch
  have capacity' := capacity.trans capAt
  obtain ⟨μ,measured,dst,won,saved,_,_,_,panel,scan,_,_,_,_,_,_,_,⟨hdr,xs,packetRead⟩,_⟩:=
    DateInputs.fromNamed_packet_entry (B:=B) accepted drift degree payload e previous M nextM oldLanes
      primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
      initial prepared sceneRoom degreeAt ready mem gr fee capAt history branch seen popFit popRead wireRoom oldPos
      oldWidth entryFits low score census.1 degreePos headerBits hostBits ranksFit namesFit degFit laneRoom
      oldHubRoom capacity' pitch cutAt rootLanes small word ceiling
  have packing:=fromNamed_matrix_packing G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count cutAt rootLanes small word ceiling capacity'
  have nonempty : 0<DescentRotorWindowArchive.count venue.degree (2^k) venue.cap:=by
    unfold DescentRotorWindowArchive.count
    positivity
  have height : GroupStage.depthBound D n f g+2<w:=by
    let field:=(successor₀).middle.rootField
    have h₁ : field≤field*DescentRotorWindowArchive.count venue.degree (2^k) venue.cap:=
      Nat.le_mul_of_pos_right _ nonempty
    have h₂ :=Nat.le_mul_of_pos_left (max (field*DescentRotorWindowArchive.count venue.degree (2^k) venue.cap)
      (DescentRotorWindowArchive.output n (2^k) venue.cap)) (Nat.two_pow_pos e)
    have h₃ : Ht+2≤field:=packing.2.2
    have h₄ := packing.1
    change (2^e)*max (field*_) _≤w/2 at h₄
    rw [←degreeAt]
    omega
  have rd:=DateInputs.fromNamed_funded_packet (B:=B) drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom degreeAt capAt z₀ measured hdr xs packetRead ready cutAt rootLanes small word ceiling height
  obtain ⟨snap,pages⟩:=funded_reindex B input.valid.host hosts feeBanks _
    (root_snapshot B input.valid.host (im degreeAt capAt).receiver (im degreeAt capAt).book
      (im degreeAt capAt).prepared measured hdr xs) rd
  have dim : (cc-e)+(e+k)=cc+k:=by omega
  have shapeDim : (E).dim=(cc-e)+(e+k):=(sh).dimension.symm.trans dim.symm
  let basis:=cast (congrArg DescentGL.Layout shapeDim) μ
  have moved:=move_basis shapeDim μ
  have selected : HEq basis B.frame.basis:=moved.1.trans won
  have savedAt : measured (P).saved=((DescentExterior.matrixCode basis).val:Word w):=by
    simpa only [basis,moved.2] using saved
  have observed:=panel_reindex B dim basis selected hosts measured panel.panel
  have precisionEq : precision=S.censusBits p:=readBits.symm.trans oldWidth
  have positiveQuota : 0<quota S.rounds := Nat.succ_pos _
  exact fromNamed_primitive_venue_paid B drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared
    sceneRoom z₀ accepted degreeAt ready mem gr fee capAt history branch seen popFit popRead wireRoom oldPos oldWidth
    entryFits low score census.1 degreePos headerBits hostBits ranksFit namesFit degFit laneRoom hosts groups blocks
    capacity pitch (rootLanes.symm ▸ Nat.two_pow_pos e) readLanes readBits original safe banks oldHub oldAtom oldWire
    measured scan basis selected savedAt snap pages nBits observed caps.1 caps.2.1 caps.2.2.1 caps.2.2.2
    positiveQuota (precisionEq.symm ▸ census.2.1) (precisionEq.symm ▸ census.2.2) newHost newChunks atOperands

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
