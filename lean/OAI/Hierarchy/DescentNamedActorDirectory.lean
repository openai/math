import OAI.Hierarchy.DescentRecordedPublicActorDirectory
import OAI.Hierarchy.DescentFallbackActorWordRoom
import OAI.Hierarchy.DescentNamedActorReady
import OAI.Hierarchy.DescentCalendarPrivatePages

namespace OAI
/-! # The named reset runs its original receiver and actor classifier on the attained stencil -/
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
local notation "succ₀" => (a).successor
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
local notation "actorBase" => (succ₀).middle.stop base₀
local notation "early" => (succ₀).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (succ₀).front.SceneRoom early ((succ₀).issuedScene base₀ older) w)
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
local notation "res" => (Z).k-(T).commonDepth
local notation "rows" => (DescentDenseHostOrder.roster (Z).graph res (GroupStage.depthBound D n f g)).card
local notation "prev" => fun v=>(Z).placement.b (B.frame.host v)
local notation "U" => (succ₀).actor
local notation "dir" => (U).directory actorBase
local notation "scene" => (U).scene actorBase
local notation "pub" => (((rc).preparedRoots book prepared).seq ((U).classifier (u).actor actorBase w)).seq ((dir).program w scene)
local notation "ticks" => ((rc).preparedTicks book prepared+(U).classifierTime (u).actor actorBase w)+(dir).ticks scene

set_option maxHeartbeats 650000 in
include accepted in
/-- The same physical publication supplies both the four compact-directory words
and the typed actor, depth and level planes at its intermediate memory. -/
theorem DateInputs.fromNamed_directory (degreeAt : venue.degree=D) (ready : (u).Ready)
    (measured : Memory w)
    (old : ClosedReset.Recorded.ActorPanelAt (B:=B) (M:=2^e) (t:=tBits) (nbits:=nBits)
      count (E).depthRows (rc).stencil book measured)
    (levels : cc+k-(T).commonDepth < 2^nBits) (one : 1 < 2^nBits)
    (mass : 2^(cc+k-(T).commonDepth)*amp < 2^nBits)
    (shapeRoom : 2*DescentFallbackShapeTable.rows (cc+k-(T).commonDepth) (2^(Z).n) ≤ 2^tBits)
    (live : 0 < amp) (quotaPos : 0 < quota S.rounds) (degreePos : 0 < 32*Nat.clog 2 (2*venue.degree))
    (word : 0 < w) (ranksFit : venue.degree*2^Ht < 2^w)
    (namesFit : DescentFallbackShapeTable.actorWordBits k (32*Nat.clog 2 (2*venue.degree)) g n ≤ w)
    (hubs : HH ≤ io.hubs.size) (hosts : HH < 2^w) (degFit : venue.degree+1 < 2^w) (lanes : 2^e ≤ w) :
    ∃dst,(pub).Exec measured dst ticks ∧ dst (dir).count.base=(Fintype.card B.next.V:Word w) ∧
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
        ∀j,j < ((U).levels actorBase).size → mid (((U).levels actorBase).base+j)=((j-(T).commonDepth+1:ℕ):Word w) := by
  have initialBound : (P).base ≤ (rc).origin := ((P).S.banks (P).X (P).base (P).bank ready.stencil.operands).2.2.2.2.2.2.2.2.trans
    ((P).S.header_before_output (P).base)
  have carry {b : Bank} (h : b.Fits w (P).base) : b.Fits w (rc).origin :=
    ⟨h.1,h.2.1,h.2.2.trans initialBound⟩
  have prior:=ready.stencil.operands.old
  have dim : (E).dim=cc+k := (sh).dimension.symm
  have hostCount : (E).hosts=HH*((E).dim+1+venue.degree):=rfl
  have deep : HH*(cc+k+1) ≤ (E).depthRows.size := by
    apply le_trans _ ready.prime.fit.hostRows.1
    exact (congrArg (fun t => HH*(t+1)) dim.symm).le.trans
      ((Nat.mul_le_mul_left HH (Nat.le_add_right _ _)).trans hostCount.symm.le)
  have pre:=(rc).stencil_fits_before prepared.toPrefixFits
  obtain ⟨l₁,l₂,l₃⟩:=(book).limits (rc).projectionEnd HH (2^cc) (2^e)
  have headerEnd : (rc).headerEnd book ≤ (rc).preparedEnd book:=Nat.le_add_right ..
  have wholeLine : (rc).stencil.Fits w ((rc).preparedEnd book) :=
    ⟨pre.1,pre.2.1,pre.2.2.trans (l₁.trans (l₂.trans (l₃.trans headerEnd)))⟩
  have usedLine : (rc).stencil.base+HH*chunks (2^cc) (2^e) ≤ (rc).origin :=
    ((P).S.output_end (P).base).symm.le
  let page : DescentSixParty.Chronology.RootPage k (2^n):=(false,.inr (⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le _) (by decide)⟩,none))
  have catalog : (book).fallbackDegree=32*Nat.clog 2 (2*venue.degree) ∧ (book).hubBits=g ∧
      (book).loadBits=f ∧ (book).shapes=2^Ht := ⟨rfl,rfl,rfl,rfl⟩
  have liveRoom : (U).Ready (u).actor ((rc).preparedEnd book) w := Eq.mpr (congrArg (fun loc => (U).Ready (u).actor loc w) ready.rootEnd) ready.actor
  have output:=ClosedReset.Recorded.directory_on_public accepted board count (E).depthRows (rc).stencil rc book prepared
    (degreeAt.trans input.branch.symm) B.dimension.symm B.graph.symm (ClosedReset.Window.calendar_residual B).symm
    B.commonDepth.symm (congrArg (fun j=>GroupStage.depthBound j n f g) degreeAt) rfl rfl
    measured page old catalog levels one mass shapeRoom live quotaPos degreePos word ranksFit (DescentFallbackShapeTable.actor_shape_fits namesFit)
    (fun v=>((Z).placement.depth (B.frame.host v)).trans_eq B.frame.extent)
    (carry prior.count.1) (carry prior.levels) deep usedLine wholeLine (Nat.le_pow_clog (by decide) _)
    (carry prior.roster) ready.stencil.operands.ports (carry prior.hubs) hubs hosts degFit
    liveRoom (Nat.two_pow_pos _) lanes
  let resultAt (loc : ℕ) : Prop :=
    ∃dst,((((rc).preparedRoots book prepared).seq ((U).classifier (u).actor loc w)).seq (((U).directory loc).program w ((U).scene loc))).Exec measured dst (((rc).preparedTicks book prepared+(U).classifierTime (u).actor loc w)+((U).directory loc).ticks ((U).scene loc)) ∧ dst ((U).directory loc).count.base=(Fintype.card B.next.V:Word w) ∧
      (∀v : B.next.V,dst (((U).directory loc).inverse.base+((Z).denseHostRank T rank v).val)=((rawId v).val:Word w)) ∧
      (∀v : B.next.V,dst (((U).directory loc).ranks.base+(rawId v).val)=(((Z).denseHostRank T rank v).val:Word w)) ∧
      (∀j : Fin (HH*rows),dst (((U).directory loc).flags.base+j.val)=if ∃v,rawId v=j then 1 else 0) ∧
      (∀j,j < (rc).origin ∨ ((U).directory loc).endAddress ≤ j → dst j=measured j) ∧
      ∃mid,dst=((U).directory loc).result ((U).scene loc) mid ∧
        (∀j (p₀ : Row HH (2^(T).commonDepth) (2^e)),mid (((U).scene loc).base+j.val*(HH*chunks (2^(T).commonDepth) (2^e))+
          (row _ _ _ p₀).val)=((data (ClosedReset.Recorded.realActor (reset:=B) (ClosedReset.Window.shapes B)
            (ClosedReset.Window.rack B input.valid.host) j) p₀).val:Word w)) ∧
        (∀j,j < loc → mid j=(rc).preparedImage book prepared measured j) ∧
        (∀v,mid (((U).depths loc).base+(idx v).val)=(prev v:Word w)) ∧
        ∀j,j < ((U).levels loc).size → mid (((U).levels loc).base+j)=((j-(T).commonDepth+1:ℕ):Word w)
  exact Eq.mp (congrArg resultAt ready.rootEnd) output

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
