import OAI.Hierarchy.DescentOriginalFreshFields

namespace OAI
/-! The registered retained query and amount on the actual successor candidate bank. -/
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
local notation "issued" h:arg gr:arg => OperandMenu.queryDigit («a»:=(a)) ((hw).cable.query ((raw) h gr))
  (rot (hw).queryBits 0 h gr) (pub (hw).queryBits none h gr)
local notation "posted" f:arg h:arg gr:arg => ((((oldCell f h gr).val+((hw).cable.priceField f ((raw) h gr)).val+
  (rot (hw).fieldBits (f).succ h gr).val+(pub (hw).fieldBits (some f) h gr).val:ℕ):Cell (hw).fieldBits).val:Cell (A).valueBits)

set_option hygiene true
set_option maxHeartbeats 900000

theorem DateInputs.original_retained_amount
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
    (hx : (A₁).blocks=2^k) (hj : (A₁).candidates=totalLocal B)
    (groupsAt : (A₁).groups=S.groupCount (age+1)) (aligned : (A₁).hosts=(v).sheets.hosts)
    (archive : ∀i j,let y:=(v).operandIndex (I).operand i
      Source ((v).previous (I).operand draw base₀ i j)
        (fun h gr=>ResetOutput.signedCandidateField (A₁).signedBits y.2.1
          (fetch groupsAt hx hj aligned h gr y.1 j)) (A₁).lanes ((I).operandEntry ok actorMem))
    (h : Fin hh) (gr : Fin gg) :
    code small ((choice 0).query h gr)=issued h gr ∧
    ∀f₀:Fin 7,((choice f₀).amount h gr).val=(posted f₀ h gr).val+candidate f₀ h gr:=by
  let previousWords:=fun (f₀ : Fin 7) (j : Fin (2*(A₁).candidates)) h gr=>
    ResetOutput.signedCandidateField (A₁).signedBits f₀ (fetch groupsAt hx hj aligned h gr x₀ j)
  obtain ⟨prior,fromRegister⟩:=DateInputs.named_reached_candidate_sources (B:=B) drift degree payload e previous
    M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
    previousMeta previousArguments initial prepared sceneRoom ok actorMem hx hj groupsAt aligned archive arg x₀ node

  have rooms:=DateInputs.named_amount_rooms G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom ok
  have result:=DateInputs.amount_at_issued G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom ok actorMem x₀ arg node values name hostEq groupEq X strips signed hubWord tickets
    small choice read previousWords prior ok.placed.lanes rooms.1 rooms.2.1 rooms.2.2
  refine ⟨result.1 h gr,fun f₀=>?_⟩
  have arrived : (fun j h gr=>((previousWords f₀ j h gr).val:Cell (A₁).valueBits))=
      fun j h gr=>real f₀ j h gr:=funext fun j=>funext fun h=>funext fun gr=>fromRegister f₀ j h gr
  simpa only [arrived] using result.2 f₀ h gr

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
