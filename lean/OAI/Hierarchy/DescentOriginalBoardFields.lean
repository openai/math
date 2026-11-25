import OAI.Hierarchy.DescentOriginalFreshFields
import OAI.Hierarchy.DescentNamedPublicSocketConfig
import OAI.Hierarchy.DescentOriginalPublicOperandBoard
import OAI.Hierarchy.DescentIssuedSocketNumber

namespace OAI
/-! # Reading either original source on its immutable measured board -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1200000
set_option maxRecDepth 6144
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
local notation:max "menuRow" shape:arg h0:arg g0:arg =>
    Config.relabel shape B.dimension.symm ((rowData) h0 g0)
local notation:max "pubReq" shape:arg =>
    finProdFinEquiv ((arg).cast (congrArg (fun c:Config=>c.args) shape),(node).cast (congrArg (fun c:Config=>c.nodes) shape))
local notation:max "surface" shape:arg width:arg digit:arg h0:arg g0:arg =>
    (K).column B.reset.graph width digit (pubReq shape) (menuRow shape h0 g0)
local notation:max "privateReg" shape:arg width:arg digit:arg h0:arg g0:arg =>
    ((K).rotor.flatReg B.reset.graph (K).multiplicity (K).grain (K).split node.val arg.val digit ((K).reg (menuRow shape h0 g0)):Cell width)

set_option hygiene true

include accepted in
theorem DateInputs.original_board_fields
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
    (degreeAt : venue.degree=D) (capAt : input.placement.cap=capacity₀)
    (calibrated : z=S.grainAt G.b p (age+1)) (rh : Fin hh) (rg : Fin gg) :
    ∃ shape:(cfg)=K,
      (∀ (host : H₀) word size mark number,PublicSocket B host (B.reset.unit/p) word mark number →
        (K).mixed B.reset.graph node.val arg.val (menuRow shape rh rg)=some (number,word,size,mark) →
        code small ((choice 0).query rh rg)=surface shape (hw).queryBits none rh rg ∧
        ∀digit,((choice digit).amount rh rg).val=
          (surface shape (A).valueBits (some digit) rh rg).val+candidate digit rh rg) ∧
      (privateReg shape (hw).queryBits 0 rh rg≠0 →
        code small ((choice 0).query rh rg)=privateReg shape (hw).queryBits 0 rh rg ∧
        ∀digit,((choice digit).amount rh rg).val=
          (privateReg shape (A).valueBits digit.succ rh rg).val+candidate digit rh rg) :=by
  obtain ⟨graphAt,shapeAt⟩:=DateInputs.fromNamed_public_socket_config (B:=B) accepted drift degree payload
    e previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut
    count previousMeta previousArguments initial prepared sceneRoom degreeAt capAt calibrated
  rw [←funded_units B accepted calibrated] at shapeAt
  refine ⟨shapeAt,?_,?_⟩
  · intro host word size mark number socket hit
    have bitsEq : (A).queryBits = (hw).queryBits := rfl
    have room : 2*totalLocal B < 2^(hw).queryBits := by
      rw [←hj]
      exact small.trans_eq (congrArg (2^·) bitsEq)
    have positive : surface shapeAt (hw).queryBits none rh rg ≠ 0 :=
      socket.query_live (B:=B) room
        (arg.cast (congrArg (fun c : Config => c.args) shapeAt))
        (node.cast (congrArg (fun c : Config => c.nodes) shapeAt)) (menuRow shapeAt rh rg) hit
    have retained (bits₁ : ℕ) (digit : Option (Fin 7)) : surface shapeAt bits₁ digit rh rg=pub bits₁ digit rh rg:=
      Config.column_relabel shapeAt B.dimension.symm rfl graphAt _ arg node bits₁ digit
    have sourcePositive : pub (hw).queryBits none rh rg ≠ 0 :=
      fun zero => positive ((retained _ _).trans zero)
    have sourceHit := (Config.mixed_relabel shapeAt B.dimension.symm rfl graphAt
      ((rowData) rh rg) arg.val node.val).symm.trans hit
    have amount:=DateInputs.original_public_amount (B:=B) drift degree payload e previous M nextM oldLanes
      primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
      initial prepared sceneRoom ok actorMem x₀ arg node values name hostEq groupEq X strips signed hubWord tickets
      small choice read observed hx hj groupsAt aligned archive rh rg sourceHit sourcePositive
    exact ⟨amount.1.trans (retained _ _).symm,fun digit=>by rw [retained];exact amount.2 digit⟩
  · intro positive
    have flattened (width : ℕ) (digit : Fin 8) :
        privateReg shapeAt width digit rh rg=rot width digit rh rg:=
      congrArg (fun j : ℕ=>(j:Cell width)) (Config.flat_relabel shapeAt B.dimension.symm rfl graphAt _ arg.val node.val digit)
    have sourcePositive : rot (hw).queryBits 0 rh rg ≠ 0 :=
      fun zero => positive ((flattened _ _).trans zero)
    have amount:=DateInputs.original_rotor_amount (B:=B) drift degree payload e previous M nextM oldLanes
      primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
      initial prepared sceneRoom ok actorMem x₀ arg node values name hostEq groupEq X strips signed hubWord tickets
      small choice read observed hx hj groupsAt aligned archive rh rg sourcePositive
    exact ⟨amount.1.trans (flattened _ _).symm,fun digit=>by rw [flattened];exact amount.2 digit⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
