import OAI.Hierarchy.DescentOriginalSocketHeader
import OAI.Hierarchy.DescentOriginalSocketHome
import OAI.Hierarchy.DescentCapturedRelayRows
import OAI.Hierarchy.DescentClosedResetSlotCount
import OAI.Hierarchy.DescentResetOriginalOperandSite

namespace OAI
/-! # The recorded input header of either leg of a fresh relay -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentActorRaster DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
variable {F Pin : Type} [Field F] {d : ℕ} {abits : Pin→ℕ} {W : MarkedWorld F d Pin abits}
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
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤laneBits (S.groupWidth k tail age+k) payload (S.localWalshBits p (S.groupWidth k tail age+k) f (quota S.rounds))-k) (fitsSigned : e≤previous) (fitsCut : previous≤S.groupWidth k tail age) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool)
local notation "datedInput" pr:arg sc:arg => I₀ previousMeta previousArguments initial pr sc
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx

-- These notations refer to the explicit date and operand parameters below.
set_option hygiene false
local notation "u" => datedInput prepared sceneRoom
open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage

open DescentSortedRoster

open CandidateFront ClosedReset.Window DescentSortedRoster DescentResetLocalRoster DescentResetCandidatePair
open DescentFallbackPeriod.Projected DescentResetRankedWindows DescentResetOriginalSlots DescentContactDonorFront
open DescentPackedPrivateMenu DescentResetGates DescentGL
open DescentSharedCableNames
local notation "A₁" => (v).receiver
local notation "ST" => (v).sheetsStart base₀
local notation "plan" => (v).linkedRankInputs (u).sectors ST
local notation "draw" => (v).renderFromRanks plan base₀
local notation "physicalRack" => rackOf B (((Z).denseHostRank T rank).trans (Fin.castLEEmb B.next.valid.host))
open DescentResetTrunks

local notation "fetch" gg:arg hx:arg hj:arg peers:arg h:arg gr:arg x:arg j:arg =>
  ((physicalRack (((h):Fin (A₁).hosts).cast peers)).bind (fun z=>
    candidateRows B (fieldNames B) ((((gr):Fin (A₁).groups).cast gg,z),((x):Fin (A₁).blocks).cast hx)
      (((j):Fin (2*(A₁).candidates)).cast (congrArg (2*·) hj))))

local notation "I" => u
open DescentPackedZip DescentResetOperandSetup
local notation "hw" => (v).setup
local notation "r₀" => (hw).retained
local notation "hh" => (hw).placement.newHosts
local notation "gg" => (hw).placement.groups
local notation "base" => (v).operandFloor base₀
local notation "m" => (I).beforeSetupImage ok actorMem
local notation "cfg" => publicOperands (I).atlas (I).roots (I).menu.payload
local notation "x" => x₀.cast (I).operandBlocks
local notation "ctrl" => (v).controlRegisters
local notation "controls" => (v).controlFloor base₀
local notation "actor" => (v).actor
local notation "origin" => (v).middle.stop base₀
local notation "active" => (ctrl).live controls (x).val
local notation "reg" => (ctrl).ports controls ((a).c/2) (x).val ((actor).directory origin).inverse
    ((actor).depths origin) ((actor).levels origin)
local notation "ports" => OperandMenu.publicPorts («a»:=(a)) (I).shape start (I).count (I).hub (I).g (I).Y active reg
local notation "s" => (I).bank
local notation "Ys" => (hw).assignedDigits hostEq groupEq (s).which X strips
local notation "raw" => (hw).carriedRow (s) name (Ys) signed x arg node hubWord tickets
local notation "rowData" => (I).menu.publicData (I).shape start (I).count (I).hub (I).g (I).Y active reg values rfl (x).val
local notation "dst" => ((hw).code base w (s) (I).laws).image m
local notation "ord" f:arg => (v).operandOrdinal (I).operand f arg x₀ node

open DescentSixParty.Chronology.DatePorts DescentOperandCandidateLookup

local notation "A" => (v).receiver
local notation "realFields" => DateInputs.IssuedFieldsAt G S board k tail age p f g drift degree payload e previous
  M nextM C packet oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut
  count previousMeta previousArguments initial prepared sceneRoom ok actorMem x₀ arg node values name hostEq groupEq
  X strips signed hubWord tickets



local notation "K" => publicOperandConfig B (hw).rotorBits (hw).queryBits M (B.reset.unit/p) (B.reset.unit/p)
    S.retainedNodes (S.retainedArgumentsAt G drift) p
local notation "capacity₀" => ((capCalendar G.b S.rounds g S.height).take age).prod*256
open DescentResetPublicOperandBook
local notation "menuRow" shape:arg h0:arg g0:arg =>
    Config.relabel shape B.dimension.symm ((rowData) h0 g0)

open DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentCompiler
open DescentResetTrunks DescentRotor DescentChosenRouter DescentRouterBank DescentResetAttachments
open DescentNamedContact DescentPrimitivePalette Chronology Computability.BorderVNP.Crossing
open DescentStageEdgeReceipt ThreeFlat.Routing
local notation "split_" => geoShape.granular B.count (z*G.b) B.fit hp (B.unit ▸ pos) (B.unit ▸ whole)
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "unit" => B.reset.unit/p
local notation "splitEq" => ((Nat.div_mul_cancel whole).symm : B.reset.unit=unit*p)
local notation "installed" => reentryWorldShape split_ B.reset B.terminals birth _ hp splitEq (resetMenu B) one hwWide
local notation "after_" => WorldShape.follow hp pos whole B.reblock B.cuts installed
local notation "next_" => (resetArchive B p hp whole priorArchive).bit
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "dense" => (B.reset.rawHostRank B.terminals vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=S.groupCount (age+1))) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite

open DescentSharedCableNames DescentParallelBase DescentNextSignedWindow DescentOperandStateBanks
local notation "result" chosenRank:arg pin:arg args:arg outputNode:arg j:arg => Reached.argumentPointer B.next next_ chosenRank after_ hp pin args outputNode j

local notation "sourceLoc" h0:arg g0:arg => operandLocation B (x₀.cast hx) (((h0):Fin (A₁).hosts).cast aligned)
  (((g0):Fin (A₁).groups).cast groupsAt)
local notation "actualRank" => DescentLocalArchiveOrder.reset B p hp whole priorArchive
local notation "f₇" f4:arg => ((f4):Fin 4).castLE (by decide : 4≤7)

open DescentCommonHost DescentDenseHostOrder DescentRelativeContacts DescentRetainedRangeDigits
local notation "old_" => W.granular B.count (z*G.b) B.fit
local notation "edge_" => (old_).graph.Edge
local notation "land" edge:arg => (T).home ((old_).graph.dst edge)
local notation "target" edge:arg => (blocks B).dst (trunkParent B (land edge))
local notation "short_" edge:arg => (shortName (T).commonDepth ((T).code (land edge))).2
local notation "stamp_" => (Z).k-(T).commonDepth
local notation "depth_" => GroupStage.depthBound D n f g
local notation "rowProof" edge:arg row:arg => OriginalRelayRows (field:=(hw).rotorBits) (query:=(hw).queryBits)
  (lanes:=M) (batches:=unit) (split:=unit) (nodes:=S.retainedNodes) (args:=S.retainedArgumentsAt G drift)
  (grain:=p) (M:=M) B edge row
local notation "prev" row:arg => (K).oldConfig.header ((K).basic row)

set_option hygiene true
set_option maxHeartbeats 1200000

include accepted in
theorem DateInputs.original_relay_header
    (prepared : (rc).PreparedFits book)
    (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (ok : (I).Ready) (actorMem : Memory w) {N : ℕ}
    (x₀ : Fin (v).receiver.blocks) (arg : Fin (r₀).args) (node : Fin (r₀).nodes)
    (values : (ports).Values hh gg)
    (name : Fin N→Fin (hw).placement.sparse)
    (hostEq : (hw).placement.oldHosts=(r₀).hosts) (groupEq : (hw).placement.groups*(hw).placement.blocks=(r₀).grouped)
    (X : (hw).seven.Packets) (strips : (r₀).Strips)
    (signed : Fin (hw).strip→Fin (hw).placement.oldHosts→Fin ((hw).placement.groups*(hw).placement.blocks)→Cell (hw).signedBits)
    (hubWord : Fin hh→Fin gg→Cell (hw).fieldBits) (tickets : Fin (hw).strip→Fin hh→Fin gg→Cell (hw).fieldBits)
    (small : 2*(A).candidates<2^(A).queryBits)
    (choice : ∀f₀:Fin 7,OrdinalRead (I) ok small actorMem (ord f₀)) (read : realFields)
    (observed : (I).PublicValuesRead ok actorMem x rfl name values)
    (hx : (A₁).blocks=2^k) (hj : (A₁).candidates=totalLocal B)
    (groupsAt : (A₁).groups=S.groupCount (age+1)) (aligned : (A₁).hosts=(v).sheets.hosts)
    (archive : ∀i j,let y:=(v).operandIndex (I).operand i
      Source ((v).previous (I).operand draw base₀ i j)
        (fun h gr=>ResetOutput.signedCandidateField (A₁).signedBits y.2.1
          (fetch groupsAt hx hj aligned h gr y.1 j)) (A₁).lanes ((I).operandEntry ok actorMem))
    {R : ℕ} (hp : 0<p) (one : 1≤R) (pos : 0<B.reset.unit) (whole : p∣B.reset.unit)
    (hwWide : max 1 (max B.reset.width (C*B.reset.width))≤R) (priorArchive : Archive W)
    (geoShape : WorldShape p R priorArchive.bit)
    (degreeAt : venue.degree=D) (capAt : input.placement.cap=capacity₀)
    (calibrated : z=S.grainAt G.b p (age+1)) (heightPos : 0<S.height) (growth : G.b≤2^S.capGain)
    (rh : Fin hh) (rg : Fin gg) (oldRank : Local priorArchive.bit) (pin : Pin→ℕ) (arity : ℕ) :
    ∃ shape:(cfg)=K,∀ (y : NodeOrder.All next_) (edge : edge_),
      let row:=menuRow shape rh rg
      resetOrigin B hp whole priorArchive y=.inr (.inl edge) →
      arg.val<(occurrences ((after_).sites y.1) y.2).length →
      node.val=(actualRank oldRank y.1 y.2).val →
      sourceLoc rh rg=some (DescentSharedCableNames.Stage.home B.next.placement y.1) →
      0<age → SourceSorted W input.order → rowProof edge row →
      ∀ tag:↥(roster (Z).graph stamp_ depth_),
        ((prev row) 0).val≠0 → ((prev row) 1).val=input.placement.cap →
        ((prev row) 2).val=(localRank (Z).graph stamp_ depth_ tag).val →
        tag.val=.trunk true ((),short_ edge) →
        ∀digit:Fin 4,((choice (f₇ digit)).amount rh rg).val=
          (result (actualRank oldRank) pin arity y arg.val).header digit :=by
  obtain ⟨shape,socketField⟩:=DateInputs.original_socket_header (B:=B) accepted drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
    previousArguments initial prepared sceneRoom ok actorMem x₀ arg node values name hostEq groupEq X strips signed
    hubWord tickets small choice read observed hx hj groupsAt aligned archive hp one pos whole hwWide priorArchive
    geoShape degreeAt capAt calibrated heightPos growth rh rg oldRank pin arity
  refine ⟨shape,?_⟩
  intro y edge row emittedAt bound numbered place elapsed sorted captured tag liveRequest capRead tagRead readKind
  obtain ⟨snap,rows⟩:=captured
  let slot : Fin (2*unit):=⟨arg.val,bound.trans_le (le_of_eq
    (relay_slot_count B hp one pos whole hwWide priorArchive geoShape y edge emittedAt))⟩
  have posId:=numbered.trans (relay_node_number B hp whole priorArchive oldRank y edge emittedAt)
  obtain ⟨number,socket,face,orientation,reply⟩:=RelayRows.reply B input.valid.host (Fin.valEmbedding (n:=S.groupCount age))
    snap B.next.valid.host elapsed sorted edge slot row rows tag liveRequest tagRead readKind capRead rfl
  have entry:=relay_flat_key B hp one pos whole hwWide priorArchive geoShape y edge emittedAt slot
  have siteAt:=relay_original_site B hp whole priorArchive y edge emittedAt
  have address:target edge=DescentSharedCableNames.Stage.home B.next.placement y.1:=by
    change DescentSharedCableNames.Stage.home B.next.placement ((hop) ((coarse).graph.dst (trunkParent B (land edge))))=_
    rw [←siteAt]
    exact congrArg (DescentSharedCableNames.Stage.home B.next.placement) ((hop).apply_symm_apply y.1)
  apply socketField y (target edge) _ 1 _ number socket (by simpa only [address] using place)
  · simpa only [posId] using reply
  · rw [face]
    exact entry
  · exact socket.original_site B y.1 address

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
