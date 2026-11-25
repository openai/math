import OAI.Hierarchy.DescentPostedPaidActors
import OAI.Hierarchy.DescentNamedActorClassWord
import OAI.Hierarchy.DescentPaidResidentCensus
import OAI.Hierarchy.DescentPackedCensusInvoice

namespace OAI
/-! Genuine directory, census and primitive class at an attained named reset. -/

namespace Hierarchy.DescentPrimitiveBirth.Layout
open DescentCompiler DescentSIMDLookup
private theorem host_room {w base : ℕ} (z : Layout) (live : 0<z.placement.parts)
    (roof : z.lifted base<2^w) : z.placement.newHosts≤2^w:=by
  let P:=z.placement
  have rr : P.rows≤DescentResetRetainedPlacement.Chart.rounded P.rows:=
    (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  calc z.placement.newHosts≤P.rows:=Nat.le_mul_of_pos_right _ live
       _≤DescentResetRetainedPlacement.Chart.rounded P.rows:=rr
       _≤z.lifted base:=Nat.le_add_left _ _
       _≤2^w:=roof.le
end Hierarchy.DescentPrimitiveBirth.Layout

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
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
local notation "namedSuccessor" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤wide-k) (fitsSigned : e≤previous) (fitsCut : previous≤cc) (count : Bank)
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
local notation "actorBase" => (namedSuccessor).middle.stop base₀
local notation "early" => (namedSuccessor).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (namedSuccessor).front.SceneRoom early ((namedSuccessor).issuedScene base₀ older) w)
local notation "u" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx
local notation "rawId" => (Z).rawHostRank T rank
local notation "HH" => S.hostSize age

open ClosedReset.Window DescentResetActorClass DescentResetDenseOperand
local notation "D₀" => (namedSuccessor).actor.directory actorBase
local notation "A₀" => (namedSuccessor).actorClass
local notation "L₀" => (namedSuccessor).birth.placement
local notation "K₀" => (namedSuccessor).birth.classBits
local notation "res" => (Z).k-(T).commonDepth
local notation "num" => Fintype.card B.next.V
local notation "earlyName" => originalCompactName B HH input.valid.host
local notation "roleAt" => (namedSuccessor).fullEnd base₀
local notation "movedAt" => (namedSuccessor).roleEnd base₀
local notation "classAt" => (namedSuccessor).classEnd base₀
variable (z₀ : (u).FinalInputs)

local notation "expected" key:arg => (Fin.cast (congrArg (fun b : ℕ=>2^b) (show K₀=indexBits (Z).n res from by
  change indexBits n k=_
  rw [B.dimension,calendar_residual B]).symm)
  ((paidActorAt B key).elim 0 (fun actor=>indexed (Z).graph res actor.val)))

local notation "nBits" => k+S.localWalshBits p (cc+k) f (quota S.rounds)+2
local notation "tBits" => 2*k+n+2
local notation "amp" => input.placement.wire*(input.placement.z*G.b)*input.placement.cap

local notation "entry₀" => (a).ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)


variable (accepted : B.Recorded p)

include accepted in
theorem fromNamed_primitive_venue (degreeAt : venue.degree=D) (blocksAt : venue.k=k) (hostsAt : venue.hosts=HH)
    (positiveBatch : 0<M)
    (ready : (u).Ready) (safe : z₀.Room) (mem : Memory w)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (capAt : input.placement.cap=cap) (history : hist=S.firstWidth G.b p) (branch : G.b≤2^S.capGain)
    (seen : stageVenue input input.valid.host io (namedSuccessor).funded.oldLanes (namedSuccessor).funded.precision floor
      (input.venueRoster input.valid.host) mem) (popFit : count.Fits w floor)
    (popRead : mem count.base=(Fintype.card input.V:Word w))
    (wireRoom : ∀(x:DescentColonies.Block k)(j:Fin (2*input.placement.cap)),(io.wire x.val j.val).Fits w floor ∧
      HH*chunks (S.groupCount age) (namedSuccessor).funded.oldLanes≤(io.wire x.val j.val).size)
    (oldPos : 0<(namedSuccessor).funded.oldLanes) (oldWidth : (namedSuccessor).funded.precision=S.censusBits p)
    (entryFits : start<2^w) (low : k≤(E).low)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (live : 0 < amp) (degreePos : 0 < 32*Nat.clog 2 (2*venue.degree))
    (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p) ≤ w) (hostBits : HH < 2^w)
    (ranksFit : venue.degree*2^Ht < 2^w)
    (namesFit : DescentFallbackShapeTable.actorWordBits k (32*Nat.clog 2 (2*venue.degree)) g n ≤ w)
    (degFit : venue.degree+1 < 2^w) (laneRoom : 2^e ≤ w)
    {snapshot:Memory w} (atOperands:(u).throughOperandDate.Runs ((entry₀).image mem) snapshot) :
    (namedSuccessor).metadata.chart.blocks≤2^(namedSuccessor).venue.next.k ∧
    0<(namedSuccessor).birth.sourceLanes ∧
    z₀.venueImage snapshot (D₀).count.base=(num:Word w) ∧
    (∀j:Fin num,z₀.venueImage snapshot ((D₀).inverse.base+j.val)=((earlyName j).val:Word w)) ∧
    num<2^w ∧ (L₀).newHosts≤2^w ∧ num≤(D₀).inverse.size ∧
    (∀site,(B.next.placement.records site).length<2^(namedSuccessor).birth.paidBits) ∧
    Source (FinalInputs.classWord u) (fun (h:Fin (L₀).newHosts) (_:Fin (L₀).groups)=>expected h)
      (L₀).lanes (z₀.classImage snapshot):=by
  obtain ⟨_,cnt,inv,_⟩:=DateInputs.fromNamed_operand_actors accepted drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
    previousArguments initial prepared sceneRoom degreeAt ready mem gr fee capAt history branch seen popFit popRead
    wireRoom oldPos oldWidth entryFits low score live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom atOperands
  obtain ⟨_,_,saved,narrow,_,cntFits,invFits,_⟩:=DateInputs.fromNamed_held_bounds B p drift degree payload e
    previous M nextM oldLanes primitiveLanes printedBits venue io floor w (u) ready degreeAt blocksAt hostsAt capAt positiveBatch
  have counted:= (z₀.venue_prior_frame safe snapshot _ cntFits).trans cnt
  have inverse (j : Fin num) : z₀.venueImage snapshot ((D₀).inverse.base+j.val)=((earlyName j).val:Word w):=by
    let actor:=(denseOrder B).symm j
    have key : B.next.vertex actor=j := (denseOrder B).apply_symm_apply j
    have below:=((Nat.add_lt_add_left j.isLt (D₀).inverse.base).trans_le invFits)
    apply (z₀.venue_prior_frame safe snapshot _ below).trans
    have read := inv actor
    change snapshot ((D₀).inverse.base+(B.next.vertex actor).val)=((rawId actor).val:Word w) at read
    rw [←installed_compact_name B input.valid.host actor,key] at read
    exact read
  have groupsPos:0<S.groupCount (age+1):=by rw [←S.group_power ctl.base ctl.radix];exact Nat.two_pow_pos _
  have liveParts:0<(L₀).parts:=by
    change 0<(S.groupCount (age+1)+M-1)/M
    exact Nat.div_pos (by omega) positiveBatch
  have hostRange:=DescentPrimitiveBirth.Layout.host_room (namedSuccessor).birth liveParts safe.birth.roof
  have height:0<S.height:=by
    by_contra! ended
    have none:S.height=0:=by omega
    simpa [DescentCompiler.AtomSchedule.length,none] using B.age
  have big:=(B.next.placement.census_caps_at S B.next.valid height B.age
    (B.next.grain.trans gr) (B.next.edges.trans fee) branch).2
  have amounts (site : B.reblock.result.graph.Site) :
      (B.next.placement.records site).length<2^venue.paidBits:=by
    change venue.paidBits=S.censusBits p at oldWidth
    rw [oldWidth]
    exact (DescentPaidResidentCount.record_bound B.next.placement S B.next.valid site).trans_lt big
  refine ⟨?_,Nat.two_pow_pos _,counted,inverse,narrow,hostRange,saved,amounts,?_⟩
  · change 2^k≤2^venue.k
    rw [blocksAt]
  · exact fromNamed_class_word B drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
      venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
      z₀ degreeAt snapshot safe counted inverse saved narrow hostRange

open DescentPacking.PackedMatch.Local.Stage DescentFundedCensus DescentPaidResidentCount.Reset
open DescentSharedCableNames DescentFallbackPeriod.Projected DescentSixParty.ClosedReset DescentGL DescentIssuedFallbackPanel
open DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage
local notation "st_" => (a).throughStencil (u).shape start (u).count (u).hub (u).g (u).Y
  (u).src (u).sourceRows (u).oldDegree w
local notation "time_" => (a).throughStencilTicks (u).shape start (u).count (u).hub (u).g (u).Y
  (u).sourceRows (u).oldDegree w
local notation "fund_" => (namedSuccessor).funded
local notation "bill_" => (namedSuccessor).venue.census
local notation "precision" => (bill_).bits
local notation "key_" => (⟨(P).saved,0⟩:Bank)
local notation "feeStart" => (namedSuccessor).fundedEnd base₀
local notation "feeBanks" => fundedPorts (funded_residual B) B.dimension z₀.ports
local notation "enter" src:arg => (entry₀).image src

include accepted in
/-- The same old venue, addressed root observations and measured funding run
supply both the compact directory and every successor census operand. -/
theorem fromNamed_primitive_venue_paid (degreeAt : venue.degree=D) (ready : (u).Ready) (mem : Memory w)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (capAt : input.placement.cap=cap) (history : hist=S.firstWidth G.b p) (branch : G.b≤2^S.capGain)
    (seen : stageVenue input input.valid.host io (namedSuccessor).funded.oldLanes (namedSuccessor).funded.precision floor
      (input.venueRoster input.valid.host) mem) (popFit : count.Fits w floor)
    (popRead : mem count.base=(Fintype.card input.V:Word w))
    (wireRoom : ∀(x:DescentColonies.Block k)(j:Fin (2*input.placement.cap)),(io.wire x.val j.val).Fits w floor ∧
      HH*chunks (S.groupCount age) (namedSuccessor).funded.oldLanes≤(io.wire x.val j.val).size)
    (oldPos : 0<(namedSuccessor).funded.oldLanes) (oldWidth : (namedSuccessor).funded.precision=S.censusBits p)
    (entryFits : start<2^w) (low : k≤(E).low)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (live : 0 < amp) (degreePos : 0 < 32*Nat.clog 2 (2*venue.degree))
    (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p) ≤ w) (hostBits : HH < 2^w)
    (ranksFit : venue.degree*2^Ht < 2^w)
    (namesFit : DescentFallbackShapeTable.actorWordBits k (32*Nat.clog 2 (2*venue.degree)) g n ≤ w)
    (degFit : venue.degree+1 < 2^w) (laneRoom : 2^e ≤ w)
    (hosts : HH=venue.hosts) (groups : venue.groups=S.groupCount age)
    (blocks : venue.k=k) (capacity : venue.cap=input.placement.cap) (pitch : venue.lanes=2^previous)
    (pos : 0<M) (readLanes : (fund_).oldLanes=venue.lanes) (readBits : (fund_).precision=precision)
    (original : z₀.io=io) (safe : z₀.Room) (banks : IssuedBanks io venue.hosts (S.groupCount age) venue.lanes)
    (oldHub : io.hubs.Fits w floor) (oldAtom : ∀x:Fin (2^(a).ingress.k),(io.atoms x.val).Fits w floor)
    (oldWire : ∀j:(a).ingress.signed.Slot,(io.wire j.1.val j.2.val).Fits w floor)
    (measured : Memory w) (scan : (st_).Exec (enter mem) measured time_)
    (μ : DescentGL.Layout ((cc-e)+(e+k))) (chosen : HEq μ B.frame.basis)
    (saved_ : measured (P).saved=((DescentExterior.matrixCode μ).val:Word w))
    (snap : PaddedSnapshot B (input.valid.host.trans_eq hosts) (u).roots.field)
    (rootPages : ∀s t,Source ((feeBanks).bank s t) (savedInput B (input.valid.host.trans_eq hosts) snap) (2^e)
      ((rc).preparedImage (u).book (u).bookFits measured))
    (fBits : ℕ)
    (printed : PackedFlow.Padded.Published (h:=cc-e) (l:=e+k) (2^e) (P).S.t (P).output
      (input.vertex.trans (Fin.castLEEmb (input.valid.host.trans_eq hosts)))
      (ClosedReset.Recorded.realPanel (reset:=B) (by omega : cc-e+(e+k)=cc+k) μ fBits (P).S.t) measured)
    (up : cc+k-(T).commonDepth<2^fBits) (one : 1<2^fBits) (enough : 2^(cc+k-(T).commonDepth)*amp<2^fBits)
    (legal : 2*DescentFallbackShapeTable.rows (cc+k-(T).commonDepth) (2^(Z).n)≤2^(P).S.t)
    (positiveQuota : 0<quota S.rounds) (countFits : amp<2^precision) (arrivalFits : 2*input.placement.cap<2^precision)
    (newHost:0<S.hostSize (age+1))(newChunks:0<chunks (S.groupCount (age+1)) M)
    {snapshot:Memory w} (atOperands:(u).throughOperandDate.Runs (enter mem) snapshot) :
    (namedSuccessor).metadata.chart.blocks≤2^(namedSuccessor).venue.next.k ∧
    0<(namedSuccessor).birth.sourceLanes ∧
    z₀.venueImage snapshot (D₀).count.base=(num:Word w) ∧
    (∀j:Fin num,z₀.venueImage snapshot ((D₀).inverse.base+j.val)=((earlyName j).val:Word w)) ∧
    num<2^w ∧ (L₀).newHosts≤2^w ∧ num≤(D₀).inverse.size ∧
    (∀site,(B.next.placement.records site).length<2^(namedSuccessor).birth.paidBits) ∧
    Source (FinalInputs.classWord u) (fun (h:Fin (L₀).newHosts) (_:Fin (L₀).groups)=>expected h)
      (L₀).lanes (z₀.classImage snapshot) ∧
    ∀x:DescentColonies.Block k,Source (.lookup (((namedSuccessor).venue.sources (FinalInputs.predecessor u) feeStart).paid x.val) .row)
        (fun h g=>Census.count B.next.placement (Equiv.refl _) (B.next.vertex.trans (Fin.castLEEmb B.next.valid.host))
          venue.paidBits h g x) M (z₀.venueImage snapshot):=by
  obtain ⟨all,sourceLanes,cnt,inv,narrow,room,saved,fit,kind⟩:=
    fromNamed_primitive_venue B drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
      venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom z₀
      accepted degreeAt blocks hosts.symm pos ready safe mem gr fee capAt history branch seen popFit popRead wireRoom
      oldPos oldWidth entryFits low score live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom atOperands
  refine ⟨all,sourceLanes,cnt,inv,narrow,room,saved,fit,kind,?_⟩
  have paid:=DateInputs.fromNamed_paid_venue accepted drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared
    sceneRoom z₀ degreeAt ready mem gr fee capAt history branch seen popFit popRead wireRoom oldPos oldWidth entryFits
    low score live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom hosts groups blocks capacity pitch
    pos readLanes readBits original safe banks oldHub oldAtom oldWire measured scan μ chosen saved_ snap rootPages
    fBits printed up one enough legal positiveQuota countFits arrivalFits newHost newChunks
  simpa only [(u).throughOperandDate.nextMemory_eq atOperands] using paid

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
