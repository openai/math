import OAI.Hierarchy.DescentNamedActorPanelFromVenue
import OAI.Hierarchy.DescentPhysicalResetHeadFrame
import OAI.Hierarchy.DescentPackedCensusInvoice

namespace OAI
/-! # Compact reset actors from the genuine paid input venue and the named native program -/
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
  {B : ClosedReset input ctl} (accepted : B.Recorded p)
local notation "board" => ctl.board
local notation "packet" => ctl.bitsR
variable (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
  (venue : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "nextCPU" => (a).successor
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
local notation "actorBase" => (nextCPU).middle.stop base₀
local notation "early" => (nextCPU).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (nextCPU).front.SceneRoom early ((nextCPU).issuedScene base₀ older) w)
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
local notation "priorCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal io.wire io.roster nextCPU
local notation "sourceRows" => DescentResetCanvasIngress.datedLayout input HH (nextCPU).funded.oldLanes
  (priorCPU).lanes (priorCPU).short (nextCPU).funded.precision (priorCPU).bits
local notation "oldCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal
  ((sourceRows).tokenAt floor) io.roster nextCPU
local notation "geom₀" => (a).chart start
local notation "fresh" => (geom₀).remixEnd (a).payload (a).gain (a).positive
local notation "phys₀" => DescentGLPacked.BankImage.Dated.chart (E).endAddress (geom₀).routedHosts (a).high (a).low (a).bits
local notation "saved" => fresh+(2^(E).dim)^(E).dim+(2^(E).dim)^(E).dim
local notation "chip" => ((phys₀).chosen (E).dim).bank (DescentGLNielsen.schedule (E).dim).length
local notation "digits" => S.resetInputDigits ctl.base ctl.radix age
local notation "peer₀" => PackedFlow.portAt input.placement (input.placement.numberedHeader digits input.vertex).site

local notation "res" => (Z).k-(T).commonDepth
local notation "rows" => (DescentDenseHostOrder.roster (Z).graph res (GroupStage.depthBound D n f g)).card
local notation "prev" => fun v=>(Z).placement.b (B.frame.host v)
local notation "U" => (nextCPU).actor
local notation "dir" => (U).directory actorBase
local notation "scene" => (U).scene actorBase
local notation "pub" => (((rc).preparedRoots book prepared).seq ((U).classifier (u).actor actorBase w)).seq ((dir).program w scene)
local notation "ticks" => ((rc).preparedTicks book prepared+(U).classifierTime (u).actor actorBase w)+(dir).ticks scene

local notation "entry₀" => (a).ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)

include accepted in
theorem DateInputs.fromNamed_venue_matrix (degreeAt : venue.degree=D) (ready : (u).Ready) (mem : Memory w)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (capAt : input.placement.cap=cap) (history : hist=S.firstWidth G.b p) (branch : G.b≤2^S.capGain)
    (seen : stageVenue input input.valid.host io (nextCPU).funded.oldLanes (nextCPU).funded.precision floor
      (input.venueRoster input.valid.host) mem) (popFit : count.Fits w floor)
    (popRead : mem count.base=(Fintype.card input.V:Word w))
    (wireRoom : ∀(x:DescentColonies.Block k)(j:Fin (2*input.placement.cap)),(io.wire x.val j.val).Fits w floor ∧
      HH*chunks (S.groupCount age) (nextCPU).funded.oldLanes≤(io.wire x.val j.val).size)
    (oldPos : 0<(nextCPU).funded.oldLanes) (oldWidth : (nextCPU).funded.precision=S.censusBits p)
    (entryFits : start<2^w) (low : k≤(E).low)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (live : 0 < amp) (degreePos : 0 < 32*Nat.clog 2 (2*venue.degree))
    (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p) ≤ w) (hostBits : HH < 2^w)
    (ranksFit : venue.degree*2^Ht < 2^w)
    (namesFit : DescentFallbackShapeTable.actorWordBits k (32*Nat.clog 2 (2*venue.degree)) g n ≤ w)
    (degFit : venue.degree+1 < 2^w) (laneRoom : 2^e ≤ w) :
    ∃(μ : DescentGL.Layout (E).dim) (measured dst : Memory w),HEq μ B.frame.basis ∧
      measured (P).saved=((DescentExterior.matrixCode μ).val:Word w) ∧
      (∀x<floor,measured x=mem x) ∧
      ClosedReset.Recorded.StencilReservationWords (reset:=B) E ((sh).dimension.symm.trans B.keyWidth.symm)
        venue.degree degreeAt.symm.le measured ∧
      (P).S.OldOrder (P).X (P).base (P).bank g (T).commonDepth μ measured ∧
      ClosedReset.Recorded.ActorPanelAt (B:=B) (M:=2^e) (t:=tBits) (nbits:=nBits)
        count (E).depthRows (rc).stencil book measured ∧
      ((a).throughStencil sh start count io.hubs g (2^n) ((a).ingress.source floor)
        (S.groupCount age) venue.degree w).Exec ((entry₀).image mem) measured
        ((a).throughStencilTicks sh start count io.hubs g (2^n) (S.groupCount age) venue.degree w) ∧
      (pub).Exec measured dst ticks ∧
      ((((entry₀).program.seq ((a).throughStencil sh start count io.hubs g (2^n) ((a).ingress.source floor)
        (S.groupCount age) venue.degree w)).seq pub)).Exec mem dst
          (((entry₀).ticks+(a).throughStencilTicks sh start count io.hubs g (2^n) (S.groupCount age) venue.degree w)+ticks) ∧
      dst (dir).count.base=(Fintype.card B.next.V:Word w) ∧
      (∀v : B.next.V,dst ((dir).inverse.base+((Z).denseHostRank T rank v).val)=((rawId v).val:Word w)) ∧
      (∀v : B.next.V,dst ((dir).ranks.base+(rawId v).val)=(((Z).denseHostRank T rank v).val:Word w)) ∧
      (∀j : Fin (HH*rows),dst ((dir).flags.base+j.val)=if ∃v,rawId v=j then 1 else 0) ∧
      (∀j,j < (rc).origin ∨ (dir).endAddress ≤ j → dst j=measured j) ∧
      ∃mid,dst=(dir).result scene mid ∧
        (∀j (p₀ : Row HH (2^(T).commonDepth) (2^e)),mid ((scene).base+j.val*(HH*chunks (2^(T).commonDepth) (2^e))+
          (row _ _ _ p₀).val)=((data (ClosedReset.Recorded.realActor (reset:=B) (ClosedReset.Window.shapes B)
            (ClosedReset.Window.rack B input.valid.host) j) p₀).val:Word w)) ∧
        (∀j,j < actorBase → mid j=(rc).preparedImage book prepared measured j) ∧
        (∀v,mid (((U).depths actorBase).base+(idx v).val)=(prev v:Word w)) ∧
        (∀j,j < ((U).levels actorBase).size → mid (((U).levels actorBase).base+j)=((j-(T).commonDepth+1:ℕ):Word w)) ∧
        (∀v,mid (io.hubs.base+(idx v).val)=((input.placement.hub v).toNat:Word w)) ∧
        ∀v,dst (io.hubs.base+(idx v).val)=((input.placement.hub v).toNat:Word w) := by
  have dim : (E).dim=cc+k := (sh).dimension.symm
  have range : cc+k-(T).commonDepth=k := by rw [B.commonDepth];omega
  have codes : 2*DescentFallbackShapeTable.rows k (2^n) ≤ 2^tBits :=
    DescentFallbackShapeTable.actor_shape_rows k n
  have one : 1 < 2^nBits := Nat.one_lt_two_pow (by omega)
  have levels : k < 2^nBits := Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have feeBound := (input.placement.census_caps_at S input.valid ctl.height B.age.le
    (input.grain.trans gr) (input.edges.trans fee) branch).2
  have usable : S.censusBits p ≤ S.localWalshBits p (cc+k) f (quota S.rounds) := by
    dsimp only [AtomSchedule.localWalshBits,DescentWalshPrecision.bits];omega
  have mass : 2^k*amp < 2^nBits := calc
    _ < 2^k*2^(S.censusBits p) := Nat.mul_lt_mul_of_pos_left feeBound (Nat.two_pow_pos _)
    _ ≤ 2^nBits := by rw [←pow_add];exact Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨stored,stores,spectrum,depthFit⟩ := DateInputs.fromNamed_venue_bank_room (ctl:=ctl) (p:=p)
    drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned
    fitsCut count previousMeta previousArguments initial prepared sceneRoom ready
  have «prefix»:=DateInputs.fromNamed_venue_reserved accepted drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom degreeAt ready mem gr fee capAt history branch seen popFit popRead wireRoom oldPos
    oldWidth entryFits low ready.prime.fit (by omega) ready.prime.smooth score stored stores spectrum depthFit live (by simpa only [dim,range] using mass)
    (by simpa only [dim,range] using levels) one headerBits hostBits (by simpa only [dim,range] using codes) degreePos
  obtain ⟨μ,measured,chosen,before,savedWord,earlier,reserved,ordered,panel⟩:=«prefix»
  have word : 0 < w := lt_of_lt_of_le (Nat.two_pow_pos _) laneRoom
  have issued:=DateInputs.fromNamed_directory accepted drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
    degreeAt ready measured panel (range.symm ▸ levels) one (range.symm ▸ mass) (by simpa only [range,B.dimension] using codes)
    live (Nat.zero_lt_succ _) degreePos word ranksFit namesFit seen.2.2.2.2.2.1 hostBits degFit laneRoom
  obtain ⟨posted,publication,counted,inv,fwd,flags,kept,mid,image,planes,lower,depths,popLevels⟩:=issued
  obtain ⟨ingress,_⟩ := (a).ingress.any floor io.hubs (fun x=>io.atoms x.val) (fun j=>io.wire j.1.val j.2.val) mem seen.2.2.2.2.1 (fun x=>seen.2.2.2.2.2.2.2.1 x.val)
    (fun j=>(wireRoom j.1 ⟨j.2.val,by rw [capAt];exact j.2.isLt⟩).1) entryFits
  obtain ⟨out,stencilRun,_,_⟩ := (a).throughStencil_any_framed sh start count io.hubs g (2^n) ((a).ingress.source floor)
    (S.groupCount age) venue.degree w ((entry₀).image mem) ready.prime ready.stencil
  have same : out=measured := exec_unique _ mem out measured (ingress.then stencilRun) before
  have baseBound : (P).base ≤ (rc).origin := ((P).S.banks (P).X (P).base (P).bank ready.stencil.operands).2.2.2.2.2.2.2.2.trans
    ((P).S.header_before_output (P).base)
  have limits:=(book).limits (rc).projectionEnd HH (2^cc) (2^e)
  have root : (rc).origin ≤ actorBase := by
    rw [←ready.rootEnd]
    exact (rc).origin_le_projection.trans ((limits.1.trans (limits.2.1.trans limits.2.2)).trans (Nat.le_add_right ..))
  have hubBefore (v : input.V) : io.hubs.base+(idx v).val < (rc).origin :=
    (Nat.add_lt_add_left ((idx v).isLt.trans_le seen.2.2.2.2.2.1) _).trans_le
      (ready.stencil.operands.old.hubs.2.2.trans baseBound)
  refine ⟨μ,measured,posted,chosen,savedWord,earlier,reserved,ordered,panel,same ▸ stencilRun,publication,before.then publication,counted,inv,fwd,flags,kept,
    mid,image,planes,lower,depths,popLevels,?_,?_⟩
  · intro v
    exact (lower _ ((hubBefore v).trans_le root)).trans
      ((((rc).prepared_any book prepared measured).2.2 _ (.inl (hubBefore v))).trans (panel.hubs v))
  · intro v
    exact (kept _ (.inl (hubBefore v))).trans (panel.hubs v)

include accepted in
theorem DateInputs.fromNamed_venue_directory (degreeAt : venue.degree=D) (ready : (u).Ready) (mem : Memory w)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (capAt : input.placement.cap=cap) (history : hist=S.firstWidth G.b p) (branch : G.b≤2^S.capGain)
    (seen : stageVenue input input.valid.host io (nextCPU).funded.oldLanes (nextCPU).funded.precision floor
      (input.venueRoster input.valid.host) mem) (popFit : count.Fits w floor)
    (popRead : mem count.base=(Fintype.card input.V:Word w))
    (wireRoom : ∀(x:DescentColonies.Block k)(j:Fin (2*input.placement.cap)),(io.wire x.val j.val).Fits w floor ∧
      HH*chunks (S.groupCount age) (nextCPU).funded.oldLanes≤(io.wire x.val j.val).size)
    (oldPos : 0<(nextCPU).funded.oldLanes) (oldWidth : (nextCPU).funded.precision=S.censusBits p)
    (entryFits : start<2^w) (low : k≤(E).low)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (live : 0 < amp) (degreePos : 0 < 32*Nat.clog 2 (2*venue.degree))
    (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p) ≤ w) (hostBits : HH < 2^w)
    (ranksFit : venue.degree*2^Ht < 2^w)
    (namesFit : DescentFallbackShapeTable.actorWordBits k (32*Nat.clog 2 (2*venue.degree)) g n ≤ w)
    (degFit : venue.degree+1 < 2^w) (laneRoom : 2^e ≤ w) :
    ∃measured dst,
      ((a).throughStencil sh start count io.hubs g (2^n) ((a).ingress.source floor)
        (S.groupCount age) venue.degree w).Exec ((entry₀).image mem) measured
        ((a).throughStencilTicks sh start count io.hubs g (2^n) (S.groupCount age) venue.degree w) ∧
      (pub).Exec measured dst ticks ∧
      ((((entry₀).program.seq ((a).throughStencil sh start count io.hubs g (2^n) ((a).ingress.source floor)
        (S.groupCount age) venue.degree w)).seq pub)).Exec mem dst
          (((entry₀).ticks+(a).throughStencilTicks sh start count io.hubs g (2^n) (S.groupCount age) venue.degree w)+ticks) ∧
      dst (dir).count.base=(Fintype.card B.next.V:Word w) ∧
      (∀v : B.next.V,dst ((dir).inverse.base+((Z).denseHostRank T rank v).val)=((rawId v).val:Word w)) ∧
      (∀v : B.next.V,dst ((dir).ranks.base+(rawId v).val)=(((Z).denseHostRank T rank v).val:Word w)) ∧
      (∀j : Fin (HH*rows),dst ((dir).flags.base+j.val)=if ∃v,rawId v=j then 1 else 0) ∧
      (∀j,j < (rc).origin ∨ (dir).endAddress ≤ j → dst j=measured j) ∧
      ∃mid,dst=(dir).result scene mid ∧
        (∀j (p₀ : Row HH (2^(T).commonDepth) (2^e)),mid ((scene).base+j.val*(HH*chunks (2^(T).commonDepth) (2^e))+
          (row _ _ _ p₀).val)=((data (ClosedReset.Recorded.realActor (reset:=B) (ClosedReset.Window.shapes B)
            (ClosedReset.Window.rack B input.valid.host) j) p₀).val:Word w)) ∧
        (∀j,j < actorBase → mid j=(rc).preparedImage book prepared measured j) ∧
        (∀v,mid (((U).depths actorBase).base+(idx v).val)=(prev v:Word w)) ∧
        (∀j,j < ((U).levels actorBase).size → mid (((U).levels actorBase).base+j)=((j-(T).commonDepth+1:ℕ):Word w)) ∧
        (∀v,mid (io.hubs.base+(idx v).val)=((input.placement.hub v).toNat:Word w)) ∧
        ∀v,dst (io.hubs.base+(idx v).val)=((input.placement.hub v).toNat:Word w) := by
  obtain ⟨_,measured,posted,_,_,_,_,_,_,issued⟩ := DateInputs.fromNamed_venue_matrix accepted
    drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w
    fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
    degreeAt ready mem gr fee capAt history branch seen popFit popRead wireRoom oldPos oldWidth entryFits low
    score live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom
  exact ⟨measured,posted,issued⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
