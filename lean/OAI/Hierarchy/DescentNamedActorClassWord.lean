import OAI.Hierarchy.DescentNamedMeasuredActorMemory
import OAI.Hierarchy.DescentNamedCapturedActorBounds
import OAI.Hierarchy.DescentDatedRootRegisterJoin
import OAI.Hierarchy.DescentDatedRolePriorFrames

namespace OAI
/-! # The indexed birth class read by the selected named reset -/
namespace Hierarchy.DescentResetActorClass
open DescentDenseHostOrder
noncomputable section
theorem indexBook_height {n h : ℕ} (board : NonlinearExpanders.Graph n h) (H r : ℕ)
    {d d' : ℕ} (same : d=d') (key : Fin (H*(DescentDenseHostOrder.roster board r d).card)) :
    indexBook board H r d' (key.cast (congrArg (fun t=>H*(DescentDenseHostOrder.roster board r t).card) same)) =
      indexBook board H r d key := by
  subst d'
  rfl
end
end Hierarchy.DescentResetActorClass

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler
noncomputable section
variable {F X : Type} [Field F] {d : ℕ} {abits : X→ℕ} {W : MarkedWorld F d X abits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k i z wire hist D n h C f g cut tail : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

theorem installed_compact_name {H : ℕ} (pad : Fintype.card input.V≤H) (v : B.next.V) :
    originalCompactName B H pad (B.next.vertex v)=
      B.reset.rawHostRank B.terminals (B.frame.host.symm.toEmbedding.trans (input.vertex.trans (Fin.castLEEmb pad))) v := by
  have old:=originalCompactName_read B H pad v
  have same:=Fin.ext (dense_physical B pad v)
  exact same ▸ old

end
end Hierarchy.DescentSixParty.ClosedReset.Window

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

theorem fromNamed_class_size : K₀=indexBits (Z).n res := by
  change indexBits n k=_
  rw [B.dimension,calendar_residual B]

local notation "expected" key => (Fin.cast (congrArg (fun b : ℕ=>2^b) (show K₀=indexBits (Z).n res from by
  change indexBits n k=_
  rw [B.dimension,calendar_residual B]).symm)
  ((paidActorAt B key).elim 0 (fun actor=>indexed (Z).graph res actor.val)))

/-- The existing count and inverse registers determine the finite class of every
occupied rack and give zero at every padded rack. The classifier is taken from the
actual named atlas installed at the role-transfer boundary. -/
theorem fromNamed_class_word (degreeAt : venue.degree=D) (mid : Memory w) (safe : z₀.Room)
    (countAt : z₀.venueImage mid (D₀).count.base=(num:Word w))
    (inverse : ∀j : Fin num,z₀.venueImage mid ((D₀).inverse.base+j.val)=((earlyName j).val:Word w))
    (size : num≤(D₀).inverse.size) (narrow : num<2^w) (hostRoom : (L₀).newHosts≤2^w) :
    Source (FinalInputs.classWord u) (fun (h : Fin (L₀).newHosts) (_ : Fin (L₀).groups)=>expected h)
      (L₀).lanes (z₀.classImage mid) := by
  let target (j : Fin num) : Fin (A₀).rawHosts := (earlyName j).cast (by
    change HH*(DescentDenseHostOrder.roster (Z).graph res (GroupStage.depthBound D n f g)).card=HH*(DescentDenseHostOrder.roster board k Ht).card
    rw [degreeAt,B.public_hub_slots])
  have actual (actor : B.next.V) : (z₀.classKey (target (B.next.vertex actor))).val=
      (indexed (Z).graph res actor.val).val := by
    let s:=(rawId actor).cast (congrArg (HH*·) B.public_hub_slots)
    have ht : GroupStage.depthBound D n f g=Ht :=by rw [degreeAt]
    calc
      _=(indexBook board HH k Ht (s.cast (congrArg (fun t=>HH*(DescentDenseHostOrder.roster board k t).card) ht))).val := by
        change (indexBook board HH k Ht ((target (B.next.vertex actor)).cast z₀.classShape)).val=_
        unfold target
        rw [installed_compact_name B input.valid.host actor]
        rfl
      _=(indexBook board HH k (GroupStage.depthBound D n f g) s).val :=
        congrArg Fin.val (indexBook_height board HH k ht s)
      _=_:=calendar_index_at B input.valid.host actor
  have move : roleAt≤ movedAt := by
    rw [ResetOutput.roleEnd,(successor₀).roleTransfer.translate]
    exact Nat.le_add_right ..
  have born : classAt≤(successor₀).birthEnd base₀ := by
    rw [ResetOutput.birthEnd,(successor₀).birth.translate]
    exact Nat.le_add_right ..
  have prim : (successor₀).birthEnd base₀≤(successor₀).primitiveEnd base₀ := by
    rw [ResetOutput.primitiveEnd,(successor₀).primitive.translate]
    exact Nat.le_add_right ..
  have stop : (successor₀).primitiveEnd base₀≤(a).endAddress start := by
    change _≤(successor₀).metadata.endAddress _
    rw [(successor₀).metadata.translate]
    exact Nat.le_add_right ..
  have cf:=(safe.roleMove.countFit)
  have inf:=(safe.roleMove.inverseFit)
  have prior (j : ℕ) (low : j<roleAt) : z₀.retainedImage mid j=z₀.venueImage mid j :=
    ((z₀.role_input_frames safe mid).2.1 j (.inl (low.trans_le move))).symm.trans
      ((z₀.role_input_frames safe mid).2.2 j (.inl low))
  have countValue : z₀.retainedImage mid (D₀).count.base=(num:Word w) :=
    (prior _ (by have:=cf.1;have:=cf.2.2;omega)).trans countAt
  have ii (j : Fin num) : z₀.retainedImage mid ((D₀).inverse.base+j.val)=((target j).val:Word w) :=
    (prior _ ((Nat.add_lt_add_left (j.isLt.trans_le size) _).trans_le inf.2.2)).trans (inverse j)
  have seen:=((A₀).received movedAt z₀.classKey target (D₀).count (D₀).inverse (z₀.retainedImage mid)
    ⟨cf.1,cf.2.1,cf.2.2.trans move⟩ ⟨inf.1,inf.2.1,inf.2.2.trans move⟩ countValue ii size narrow hostRoom
    ((born.trans (prim.trans stop)).trans_lt safe.endFits)).2
  have values : dense (H:=(L₀).newHosts) target ((A₀).values z₀.classKey)=
      (fun (h : Fin (L₀).newHosts) (_ : Fin (L₀).groups)=>expected h) := by
    funext h g
    apply Fin.ext
    by_cases live : h.val<num
    · let actor:=(denseOrder B).symm ⟨h.val,live⟩
      have named : B.next.vertex actor=⟨h.val,live⟩ := (denseOrder B).apply_symm_apply _
      simpa only [dense,paidActorAt,dite_eq_left live,Option.elim_some,Fin.val_cast,DescentResetActorClass.Shape.values,named]
        using actual actor
    · simp [dense,paidActorAt,live]
  exact values ▸ seen

local notation "nBits" => k+S.localWalshBits p (cc+k) f (quota S.rounds)+2
local notation "tBits" => 2*k+n+2
local notation "amp" => input.placement.wire*(input.placement.z*G.b)*input.placement.cap

local notation "entry₀" => (a).ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)


variable (accepted : B.Recorded p)

include accepted in
/-- Beginning at the earlier native stage, the actual selected actor publication
supplies both the directory count and all inverse keys used by the class atlas. -/
theorem reached_class_word (degreeAt : venue.degree=D) (blocksAt : venue.k=k) (hostsAt : venue.hosts=HH)
    (positiveBatch : 0<M) (hostRoom : (L₀).newHosts≤2^w)
    (ready : (u).Ready) (safe : z₀.Room) (mem : Memory w)
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
    (live : 0 < amp) (degreePos : 0 < 32*Nat.clog 2 (2*venue.degree))
    (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p) ≤ w) (hostBits : HH < 2^w)
    (ranksFit : venue.degree*2^Ht < 2^w)
    (namesFit : DescentFallbackShapeTable.actorWordBits k (32*Nat.clog 2 (2*venue.degree)) g n ≤ w)
    (degFit : venue.degree+1 < 2^w) (laneRoom : 2^e ≤ w)
    {snapshot:Memory w} (atOperands:(u).throughOperandDate.Runs ((entry₀).image mem) snapshot) :
    Source (FinalInputs.classWord u) (fun (h : Fin (L₀).newHosts) (_ : Fin (L₀).groups)=>expected h)
      (L₀).lanes (z₀.classImage snapshot) := by
  obtain ⟨_,cnt,inv,_⟩:=DateInputs.fromNamed_operand_actors accepted drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
    previousArguments initial prepared sceneRoom degreeAt ready mem gr fee capAt history branch seen popFit popRead
    wireRoom oldPos oldWidth entryFits low score live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom atOperands
  obtain ⟨_,_,saved,narrow,_,cntFits,invFits,_⟩:=DateInputs.fromNamed_held_bounds B p drift degree payload e
    previous M nextM oldLanes primitiveLanes printedBits venue io floor w (u) ready degreeAt blocksAt hostsAt capAt positiveBatch
  apply fromNamed_class_word B drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
    z₀ degreeAt snapshot safe _ _ saved narrow hostRoom
  · exact (z₀.venue_prior_frame safe snapshot _ cntFits).trans cnt
  · intro j
    let actor:=(denseOrder B).symm j
    have key : B.next.vertex actor=j := (denseOrder B).apply_symm_apply j
    have below:=((Nat.add_lt_add_left j.isLt (D₀).inverse.base).trans_le invFits)
    apply (z₀.venue_prior_frame safe snapshot _ below).trans
    have read := inv actor
    change snapshot ((D₀).inverse.base+(B.next.vertex actor).val)=((rawId actor).val:Word w) at read
    rw [←installed_compact_name B input.valid.host actor,key] at read
    exact read

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

namespace Hierarchy.DescentSixParty.ClosedReset.Window
alias reached_class_word := DescentDatedAddressBook.PhysicalReset.reached_class_word
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
