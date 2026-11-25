import OAI.Hierarchy.DescentRegisteredPrimaryCoordinates
import OAI.Hierarchy.DescentNamedOperandRequests
import OAI.Hierarchy.DescentPhysicalOperandMenu

namespace OAI
/-! Coordinates obtained by selecting the previous host and local shape in an attained primary register. -/
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
variable {F Pin : Type} [Field F] {d : ℕ} {abits : Pin→ℕ} {W : MarkedWorld F d Pin abits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {B : ClosedReset input ctl}
local notation "board" => ctl.board
local notation "packet" => ctl.bitsR
variable (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
  (venue : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "date₀" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "stepOut" => (date₀).successor
local notation "start" => (date₀).stageStart floor
local notation "base₀" => (date₀).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤wide-k) (fitsSigned : e≤previous) (fitsCut : previous≤cc) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (date₀).rootPhase sh start count io.hubs g (2^n) roots w
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "early" => (stepOut).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (stepOut).front.SceneRoom early ((stepOut).issuedScene base₀ older) w)
local notation "u" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx

open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage

open DescentSortedRoster

open CandidateFront ClosedReset.Window DescentSortedRoster DescentResetLocalRoster DescentResetCandidatePair
open DescentFallbackPeriod.Projected DescentResetRankedWindows DescentResetOriginalSlots DescentContactDonorFront
open DescentPackedPrivateMenu DescentResetGates DescentGL
open DescentSharedCableNames
local notation "A₁" => (stepOut).receiver
local notation "ST" => (stepOut).sheetsStart base₀
local notation "plan" => (stepOut).linkedRankInputs (u).sectors ST
local notation "draw" => (stepOut).renderFromRanks plan base₀
local notation "physicalRack" => rackOf B (((Z).denseHostRank T rank).trans (Fin.castLEEmb B.next.valid.host))
open DescentResetTrunks

local notation "fetch" gg hx hj peers h gr x j =>
  ((physicalRack (((h):Fin (A₁).hosts).cast peers)).bind (fun z=>
    candidateRows B (fieldNames B) ((((gr):Fin (A₁).groups).cast gg,z),((x):Fin (A₁).blocks).cast hx)
      (((j):Fin (2*(A₁).candidates)).cast (congrArg (2*·) hj))))


local notation "I" => u
open DescentPackedZip DescentResetOperandSetup
variable (ok : (I).Ready) (actorMem : Memory w) {N : ℕ}
local notation "hw" => (stepOut).setup
local notation "r₀" => (hw).retained
local notation "hh" => (hw).placement.newHosts
local notation "gg" => (hw).placement.groups

open DescentLocalArchiveOrder DescentKernelHistory DescentBundleHistory DescentPrimitivePalette
open DescentSixParty.Chronology DescentResetActorClass
local notation "ht" => GroupStage.depthBound D n f g
local notation "res" => (Z).k-(T).commonDepth
local notation "localShapes" => (roster (Z).graph res ht).card
variable (oldA:Archive W) (oldNum:Local oldA.bit) (hp:0<p) (whole:p∣(Z).unit)
local notation "after_" => (resetArchive B p hp whole oldA).bit
local notation "newNum" => DescentLocalArchiveOrder.reset B p hp whole oldA oldNum
variable (ports:DatePorts) (places:DatePorts.RangeRoom ports B.next after_)
  (x:Fin (2^ports.venue.k)) (node:Fin ports.nodes) (h₁:Fin ports.operandHosts) (gr:Fin ports.venue.groups)
  (now:NodeOrder.All after_) (old:NodeOrder.All oldA.bit)
  (hit:DatePorts.slotAt ports B.next after_ newNum places x node h₁ gr=some now)
  (origin:resetOrigin B hp whole oldA now=Sum.inl old)
  (degreeAt:venue.degree=D) (size:S.hostSize age*localShapes=(hw).placement.sparse)
local notation "term" => (T).home old.1
local notation "digit" => DescentFallbackShapeTable.cell res (DescentRelativeContacts.shortName (T).commonDepth ((T).code term)).2
local notation "dir" => fun j:Fin (Fintype.card B.next.V)=>((Z).rawAtIndex T rank j).cast size
local notation "homeHost" => idx (B.frame.host.symm ((T).code term).1)

private theorem prod_cast {H Q H' Q':ℕ} (host:H=H') (num:Q=Q') (size:H*Q=H'*Q')
    (v:Fin H) (j:Fin Q) : (finProdFinEquiv (v,j)).cast size=finProdFinEquiv (v.cast host,j.cast num):=by
  subst H';subst Q';rfl

private theorem equal_target_height {dim deg : ℕ} (graph : NonlinearExpanders.Graph dim deg)
    (residual : ℕ) {height₀ height₁ : ℕ} (sameHeight : height₀ = height₁)
    (i₀ : Fin (roster graph residual height₀).card) (i₁ : Fin (roster graph residual height₁).card)
    (sameIndex : i₀.val = i₁.val) :
    DescentResetActorClass.targetBook graph residual height₀ i₀ =
      DescentResetActorClass.targetBook graph residual height₁ i₁ := by
  subst height₁
  exact congrArg _ (Fin.ext sameIndex)

set_option maxHeartbeats 850000 in
include hit origin degreeAt in
theorem DateInputs.named_primary_shape :
    ∃live:h₁.val<Fintype.card B.next.V,
      let cell:=(dir) ⟨h₁.val,live⟩
      (u).bank.which ((hw).placement.shape cell)=some digit ∧
      (u).menu.keep ((hw).placement.shape cell)=true ∧
      ((hw).placement.previous cell).val=(homeHost).val ∧
      gr.val*2^k+x.val=((Z).rootBlock T (.inr term)).val ∧ node.val=(newNum now.1 now.2).val:=by
  obtain ⟨present,_,stored,host,chosen,num,atNode,_⟩:=
    registered_primary_coordinates B hp whole oldA oldNum ports places x node h₁ gr now old hit origin input.valid.host
  let actor:=(B.next.placement.pos now.1).2
  let hostFields:=(Z).hostFields T rank actor
  let same:localShapes=(hw).placement.shapes := B.public_hub_slots.trans (by
    change (roster board k ht).card=(roster board k (GroupStage.depthBound venue.degree n f g)).card
    rw [degreeAt])
  have looked:(dir) ⟨h₁.val,present⟩=finProdFinEquiv (hostFields.1,hostFields.2.cast same):=by
    change ((Z).rawAtIndex T rank _).cast size=_
    exact (congrArg (Fin.cast size) stored).trans (prod_cast rfl same size _ _)
  have shape₀:(hw).placement.shape ((dir) ⟨h₁.val,present⟩)=hostFields.2.cast same:=by
    simp only [looked,DescentResetRetainedPlacement.Chart.shape]
    exact congrArg Prod.snd (finProdFinEquiv.symm_apply_apply _)
  have oldHost:(hw).placement.previous ((dir) ⟨h₁.val,present⟩)=hostFields.1:=by
    simp only [looked,DescentResetRetainedPlacement.Chart.previous]
    exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply _)
  have target : (u).menu.target ((hw).placement.shape ((dir) ⟨h₁.val,present⟩))=some digit:=by
    rw [shape₀,(u).menu.target_book]
    change targetBook board k (GroupStage.depthBound venue.degree n f g) _=some _
    exact (equal_target_height board k (congrArg (fun d => GroupStage.depthBound d n f g) degreeAt) _ _ rfl).trans chosen
  exact ⟨present,target,(u).menu.keep_of_target _ _ target,congrArg Fin.val (oldHost.trans host),num,atNode⟩


local notation "dense" => ((Z).denseHostRank T rank).trans (Fin.castLEEmb B.next.valid.host)
variable (pitch:ports.operandHosts=S.hostSize (age+1))
  (hub:Fin hh→Fin gg→Cell (hw).fieldBits)
  (fees:Fin (2^k)→Fin (hw).strip→Fin hh→Fin gg→Cell (hw).fieldBits)
local notation "hd" => h₁.cast pitch
local notation "gd" => gr.cast places.groups.symm
local notation "bx" => x.cast (congrArg (2^·) places.radix.symm)
local notation "unit_" => W.granular B.count (z*G.b) B.fit
local notation "controls" => DateInputs.PrimaryWordsAt (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
  previousArguments initial prepared sceneRoom ok actorMem hub fees

include hit origin in
theorem DateInputs.named_primary_fee (words:controls) :
    (hub hd gd=if ((T).code term).2.2.isSome then 0 else 1) ∧
    (∀s:(unit_).graph.Edge,(T).home ((unit_).graph.dst s)=term→∀j:Fin (hw).strip,
      j.val=(incomingIndex B s).val→(fees bx j hd gd).val=earlierIncoming B s) ∧
    ((rackOf B dense hd).map (fun a=>((gd,a),bx)))=some (Stage.home B.next.placement now.1):=by
  obtain ⟨host,group,blockAt,lookup_⟩:=registered_primary_cursors B hp whole oldA oldNum ports places x node
    h₁ gr now old hit origin input.valid.host pitch
  refine ⟨?_,?_,lookup_⟩
  · exact (congrArg₂ hub host group).trans (words.1 term)
  · intro edge ind j valid
    have shifted := (congrArg (fun b => (fees b j hd gd).val) blockAt).trans
      (congrArg₂ (fun h g => (fees _ j h g).val) host group)
    exact shifted.trans (words.2.1 term edge ind j valid)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
