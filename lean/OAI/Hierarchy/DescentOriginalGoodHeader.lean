import OAI.Hierarchy.DescentOriginalRotorHeader
import OAI.Hierarchy.DescentOriginalSocketHeader
import OAI.Hierarchy.DescentClosedGoodArgumentCoverage
import OAI.Hierarchy.DescentGoodPublicArgumentKey

namespace OAI
/-! # Four registered coordinates of every occupied mounted rotor operand -/
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
local notation "at_" => (finProdFinEquiv (arg,node) : Fin (hw).members)
local notation "dst" => ((hw).code base w (s) (I).laws).image m
local notation "oldCell" f:arg h:arg k:arg => ((DescentRetainedTargetPlacement.Chart.compact (hw).placement (hw).seven.batch
  (s).primary name (Ys) ((r₀).outputID 1 f arg node) x h k).val : Cell (hw).fieldBits)
local notation "rot" width:arg f:arg h:arg k:arg => ((cfg).rotor.flatReg (I).atlas.board (cfg).multiplicity (cfg).grain (cfg).split
   node.val arg.val f ((cfg).reg ((rowData) h k)) : Cell width)
local notation "pub" width:arg f:arg h:arg k:arg => (cfg).column (I).atlas.board width f at_ ((rowData) h k)
local notation "mark" => (v).retainedHub base₀ x
local notation "fee" => (v).retainedTicket base₀ x
local notation "ord" f:arg => (v).operandOrdinal (I).operand f arg x₀ node

open DescentSixParty.Chronology.DatePorts DescentOperandCandidateLookup

local notation "A" => (v).receiver
local notation "realFields" => DateInputs.IssuedFieldsAt G S board k tail age p f g drift degree payload e previous
  M nextM C packet oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut
  count previousMeta previousArguments initial prepared sceneRoom ok actorMem x₀ arg node values name hostEq groupEq
  X strips signed hubWord tickets



local notation "real" f₀:arg j:arg h:arg gr:arg => ResetOutput.nativeCandidateField (A₁).signedBits (A₁).valueBits f₀
  (fetch groupsAt hx hj aligned h gr x₀ j)
local notation "candidate" f₀:arg h:arg gr:arg => (DescentOperandCandidateLookup.selected (choice 0).query (fun j h gr=>real f₀ j h gr) h gr).val
local notation "K" => publicOperandConfig B (hw).rotorBits (hw).queryBits M (B.reset.unit/p) (B.reset.unit/p)
    S.retainedNodes (S.retainedArgumentsAt G drift) p
local notation "H₀" => Stage.Host (Fin (S.groupCount (age+1))) B.next.V k
local notation "capacity₀" => ((capCalendar G.b S.rounds g S.height).take age).prod*256
open DescentResetPublicOperandBook
local notation "menuRow" shape:arg h0:arg g0:arg =>
    Config.relabel shape B.dimension.symm ((rowData) h0 g0)
local notation "pubReq" shape:arg =>
    finProdFinEquiv (arg.cast (congrArg (fun c:Config=>c.args) shape),node.cast (congrArg (fun c:Config=>c.nodes) shape))
local notation "surface" shape:arg width:arg digit:arg h0:arg g0:arg =>
    (K).column B.reset.graph width digit (pubReq shape) (menuRow shape h0 g0)
local notation "privateReg" shape:arg width:arg digit:arg h0:arg g0:arg =>
    ((K).rotor.flatReg B.reset.graph (K).multiplicity (K).grain (K).split node.val arg.val digit ((K).reg (menuRow shape h0 g0)):Cell width)


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
local notation "world" => B.reset.orderedOrdinary B.terminals birth
local notation "cnt" => fun e=>(coarse).graph.width e/B.reset.unit
local notation "geo" => B.reset.counts_fit B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "dense" => (B.reset.rawHostRank B.terminals vertexCode).trans Fin.valEmbedding
local notation "tape" => B.reset.nativeResetEdges B.terminals vertexCode birth
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=S.groupCount (age+1))) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "sparse" => DescentResetLocalOrder.allCode B.raw ((tape).order.trans Fin.valEmbedding) S B.valid rawSite
local notation "edgeName" => DescentPhysicalOrder.rename sparse

open DescentSharedCableNames DescentParallelBase DescentNextSignedWindow DescentOperandStateBanks
local notation "ord₁" => B.next.order.trans Fin.valEmbedding
local notation "placedHost" => Stage.Host (Fin (S.groupCount (age+1))) B.next.V k
local notation "present" siteVal:arg => (installed).sites ((hop).symm (siteVal).1)
local notation "result" rankVal:arg pinVal:arg arityVal:arg siteVal:arg argVal:arg => Reached.argumentPointer B.next next_ rankVal after_ hp pinVal arityVal siteVal argVal

local notation "before_" => BitDescription.granular W B.count (z*G.b) B.fit priorArchive.bit
local notation "pre_" => (before_).batchedReset B.reset B.terminals birth unit p hp splitEq (resetMenu B)
local notation "middle_" siteVal:arg => NodeOrder.followNames B.reblock pre_ siteVal

local notation "sourceLoc" h0:arg g0:arg => operandLocation B (x₀.cast hx) (((h0):Fin (A₁).hosts).cast aligned)
  (((g0):Fin (A₁).groups).cast groupsAt)
local notation "actualRank" => DescentLocalArchiveOrder.reset B p hp whole priorArchive
local notation "f₇" f4:arg => ((f4):Fin 4).castLE (by decide : 4≤7)


local notation "rotCfg" => rotorQueryShape B unit S.retainedNodes (hw).rotorBits (hw).queryBits M
local notation "regAt" shape:arg rh:arg rg:arg => (K).reg (menuRow shape rh rg)
local notation "shapeWidth" => (Z).k-(T).commonDepth
local notation "hgt" => GroupStage.depthBound D n f g
open DescentCommonHost DescentDenseHostOrder DescentHostDirectory DescentRotorOperandQueryROM
open DescentSharedCableNames
open DescentBatchedNodeOrder DescentRetainedRangeDigits DescentBatchedBank
local notation "sized" => (splitEq ▸ (Z).circuit :
  Hardware («K»:=F) (C₀:=C) («u»:=unit*p) (Z).placement (Z).graph (Z).positive (Z).pay)
local notation "R₀" => (Z).placement
local notation:max "sizedSite" arm:arg rootVal:arg => DescentCommonPalette.rotorSiteEquiv (Z).graph d
  (selectedRotorLayers R₀ (Z).graph (Z).positive (Z).pay sized arm rootVal) C (Z).width (unit*p)
local notation:max "installedSite" arm:arg rootVal:arg => DescentCommonPalette.rotorSiteEquiv (Z).graph d
  (selectedRotorLayers R₀ (Z).graph (Z).positive (Z).pay (Z).circuit arm rootVal) C (Z).width (Z).unit
local notation:max "selectedChip" arm:arg rootVal:arg => DescentChosenRouter.selected R₀ (Z).graph (Z).positive (Z).pay sized arm (.inl rootVal)
local notation:max "progAt" arm:arg rootVal:arg cellVal:arg => DescentBatchedBank.deviceProgram («K»:=F) (C₀:=C)
  (Z).graph (Z).positive unit p hp (R₀).contact (R₀).input (R₀).site (R₀).owner (R₀).align birth d
  (selectedChip arm rootVal) ((sizedSite arm rootVal) cellVal)
local notation:max "ordAt" arm:arg rootVal:arg cellVal:arg localVal:arg => deviceOrder («K»:=F) (C₀:=C)
  (Z).graph (Z).positive unit p hp (R₀).contact (R₀).input (R₀).site (R₀).owner (R₀).align birth d
  (selectedChip arm rootVal) ((sizedSite arm rootVal) cellVal) localVal
local notation:max "mounted" arm:arg rootVal:arg cellVal:arg => (⟨(arm,.inl rootVal),(installedSite arm rootVal) cellVal⟩ : (Z).bank.Site)
local notation:max "gateAt" arm:arg rootVal:arg cellVal:arg localVal:arg =>
  (mountedGoodNode R₀ (Z).graph (Z).positive (Z).pay (Z).circuit birth d unit p hp splitEq arm rootVal cellVal).symm localVal
set_option hygiene true

include accepted in
set_option maxHeartbeats 1800000 in
theorem DateInputs.original_good_header
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
    ∃ shape:(cfg)=K,∀(y : NodeOrder.All next_) (side : Bool) (root : (R₀).Good)
      (cell : (DescentCommonPalette.rotor (Z).graph).Site) (localNode : (progAt side root cell).Node)
      (badge : ↥(roster (Z).graph shapeWidth hgt)),
      let row:=menuRow shape rh rg
      let regs:=(K).reg row
      resetOrigin B hp whole priorArchive y=.inr (.inr ⟨mounted side root cell,gateAt side root cell localNode⟩) →
      arg.val<(occurrences ((after_).sites y.1) y.2).length →
      node.val=(ordAt side root cell localNode).val →
      sourceLoc rh rg=some (Stage.home B.next.placement y.1) →
      GoodTapRows (p:=p) (field:=(hw).rotorBits) (query:=(hw).queryBits) (lanes:=M) (nodes:=S.retainedNodes)
        (args:=S.retainedArgumentsAt G drift) (grain:=p) B side root row →
      ((K).oldConfig.header ((K).basic row) 0).val≠0 →
      (regs 1).val=((Z).goodLabel T root).val.1+1 →
      (regs 2).val%2=0 → (regs 3).val=(localRank (Z).graph shapeWidth hgt badge).val →
      badge.val=.good side ((),((Z).goodLabel T root).val.2) cell →
      ((Z).circuit side root).layers*unit≤S.retainedNodes →
      ∀digit:Fin 4,((choice (f₇ digit)).amount rh rg).val=
        (result (actualRank oldRank) pin arity y arg.val).header digit :=by
  obtain ⟨shape,privateField⟩:=DateInputs.original_rotor_header (B:=B) accepted drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w
    fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom ok actorMem x₀ arg node
    values name hostEq groupEq X strips signed hubWord tickets small choice read observed hx hj groupsAt aligned archive
    hp one pos whole hwWide priorArchive geoShape degreeAt capAt calibrated heightPos growth rh rg oldRank pin arity
  obtain ⟨shape',socketField⟩:=DateInputs.original_socket_header (B:=B) accepted drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w
    fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom ok actorMem x₀ arg node
    values name hostEq groupEq X strips signed hubWord tickets small choice read observed hx hj groupsAt aligned archive
    hp one pos whole hwWide priorArchive geoShape degreeAt capAt calibrated heightPos growth rh rg oldRank pin arity
  refine ⟨shape,?_⟩
  intro y side root cell localNode badge row regs atOrigin bound numbered place rows headerActive depth safe ranked tagged span
  let slot : Fin (occurrences ((after_).sites y.1) y.2).length:=⟨arg.val,bound⟩
  have semantic:=good_argument_entry B hp one pos whole hwWide priorArchive geoShape side root cell (K).rotor
    y localNode atOrigin slot
  have layer:=sized_layer_count R₀ (Z).graph (Z).positive (Z).pay (Z).circuit unit p splitEq side root
  rcases semantic with ⟨lane,within,fetchAt,siteAt,key⟩|external
  · have whereAt : sourceLoc rh rg=some (Stage.home B.next.placement (hop ((Z).rotorSiteAt T side root cell))) :=by
      exact place.trans (congrArg (fun posAt => some (Stage.home B.next.placement posAt))
        (((hop).apply_symm_apply y.1).symm.trans (congrArg (hop) siteAt)))
    apply privateField y side root cell within lane badge whereAt siteAt rows.capacity depth safe ranked tagged
    · have chart : actualRotorChart (p:=p) B (K).rotor=rotCfg := rfl
      simpa only [slot,numbered,layer,chart] using fetchAt
    · exact span
    · exact key
    · intro earlier found
      cases found.symm.trans atOrigin
    · exact bound.trans_eq (DescentRetainedRangeDigits.length _ _ hp)
  · obtain ⟨host,number,word,count,socketMark,socket,issued,key,ending⟩:=
      good_public_argument_key (field:=(hw).rotorBits) (query:=(hw).queryBits) (lanes:=M) (nodes:=S.retainedNodes)
        (args:=S.retainedArgumentsAt G drift) B hp one pos whole hwWide priorArchive geoShape side root cell localNode
        arg.val external row rows headerActive badge depth safe ranked tagged y atOrigin
    have home : Stage.home B.next.placement y.1=host:=by
      have places:=socket.face.property.2
      have atFace : Stage.home B.next.placement
          (hop (if socket.face.val.2 then (coarse).graph.dst socket.face.val.1 else (coarse).graph.src socket.face.val.1))=host:=by
        cases sense : socket.face.val.2
        · change (blocks B).src socket.face.val.1=host
          simpa only [sense,Bool.false_eq_true,ite_false] using places
        · change (blocks B).dst socket.face.val.1=host
          simpa only [sense,ite_true] using places
      exact (congrArg (Stage.home B.next.placement) ((hop).apply_symm_apply y.1)).symm.trans
        ((congrArg (fun posAt => Stage.home B.next.placement ((hop) posAt)) ending).symm.trans atFace)
    exact socketField y host word count socketMark number socket (place.trans (congrArg some home))
      ((congrArg (fun serial => (K).mixed (Z).graph serial arg.val row) numbered).trans issued) key ending

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
