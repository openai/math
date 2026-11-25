import OAI.Hierarchy.DescentRegisteredRangeAmount
import OAI.Hierarchy.DescentResetSpanDigits
import OAI.Hierarchy.DescentNamedIssuedOrdinal
import OAI.Hierarchy.DescentOrdinalReadAmount

namespace OAI
/-! Same-snapshot query and field values for every certified choice of the seven reset operands. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
  (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
  (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
  (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "v" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤laneBits (S.groupWidth k tail age+k) payload (S.localWalshBits p (S.groupWidth k tail age+k) f (quota S.rounds))-k) (fitsSigned : e≤previous) (fitsCut : previous≤S.groupWidth k tail age) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "P" => (a).stencilPhase sh start count io.hubs g (2^n)
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count

variable (previousMeta previousArguments : ℕ) (initial : Bool)
local notation "inputAt" pr:arg sc:arg => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial pr sc

-- These notations refer to the explicit binders of both declarations below.
set_option hygiene false
local notation "I" => inputAt prepared scene

open DescentPackedZip DescentResetOperandSetup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
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
local notation "ports" => OperandMenu.publicPorts («a» := (a)) (I).shape start (I).count (I).hub (I).g (I).Y active reg
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
local notation "plan" => (v).linkedRankInputs (I).sectors ((v).sheetsStart base₀)
local notation "render" => (v).renderFromRanks plan base₀
local notation "issued" h:arg gr:arg => OperandMenu.queryDigit («a» := (a)) ((hw).cable.query ((raw) h gr))
      (rot (hw).queryBits 0 h gr) (pub (hw).queryBits none h gr)
local notation "posted" f:arg h:arg gr:arg => ((((oldCell f h gr).val+((hw).cable.priceField f ((raw) h gr)).val+
        (rot (hw).fieldBits (f).succ h gr).val+(pub (hw).fieldBits (some f) h gr).val:ℕ) :
        Cell (hw).fieldBits).val:Cell (A).valueBits)
local notation "realFields" => DateInputs.IssuedFieldsAt G S board k tail age p f g drift degree payload e previous
  M nextM C packet oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut
  count previousMeta previousArguments initial prepared scene ok actorMem x₀ arg node values name hostEq groupEq
  X strips signed hubWord tickets


set_option hygiene true

set_option maxHeartbeats 1500000 in
/-- The original seven-field publication yields the selected range value on the same actor
memory and the same window, strips, public control registers and native query ordinal. -/
theorem DateInputs.named_issued_range_amount
    (prepared : (rc).PreparedFits book)
    (scene : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (ok : (I).Ready) (actorMem : Memory w) {N : ℕ}
    (x₀ : Fin (v).receiver.blocks) (arg : Fin (r₀).args) (node : Fin (r₀).nodes)
    (values : (ports).Values hh gg)
    (name : Fin N→Fin (hw).placement.sparse)
    (hostEq : (hw).placement.oldHosts=(r₀).hosts) (groupEq : (hw).placement.groups*(hw).placement.blocks=(r₀).grouped)
    (X : (hw).seven.Packets) (strips : (r₀).Strips)
    (signed : Fin (hw).strip→Fin (hw).placement.oldHosts→Fin ((hw).placement.groups*(hw).placement.blocks)→Cell (hw).signedBits)
    (hubWord : Fin hh→Fin gg→Cell (hw).fieldBits) (tickets : Fin (hw).strip→Fin hh→Fin gg→Cell (hw).fieldBits)
    (small : 2*(A).candidates<2^(A).queryBits)
    (read : realFields) (observed : (I).PublicValuesRead ok actorMem x rfl name values)
    (choice : ∀f₀:Fin 7,OrdinalRead (I) ok small actorMem (ord f₀))
    (live : 0<(A).lanes) (wordRoom : (I).operand.coeff*(A).lanes≤w)
    (signedRoom : (A).signedBits*(A).lanes≤w)
    (axis : Fin 3) (h : Fin hh) (gr : Fin gg) :
    let page:=DescentRetainedRangeDigits.page axis
    let blank:=observed.2.2.2.2.2.1
    let label:=observed.2.2.2.2.2.2
    let span:=(I).menu.spanValue name (Ys) ((r₀).outputID 1 page arg node) x h gr ((rowData) h gr)
      at_ page (blank h gr) (label h gr)
    ((choice page).amount h gr).val=(span.val:Cell (A).valueBits).val :=by
  dsimp only
  let page:=DescentRetainedRangeDigits.page axis
  have paid:=OrdinalRead.range_amount (I) ok small actorMem axis arg x₀ node (choice page)
    (fun h gr=>posted page h gr) (read page).2 live wordRoom signedRoom h gr
  exact paid.trans (congrArg (fun z : Cell (hw).fieldBits=>(z.val:Cell (A).valueBits).val)
    ((I).menu.issued_range_digit name (Ys) ((r₀).outputID 1 page arg node) x h gr
      ((rowData) h gr) arg node (observed.2.2.2.2.2.1 h gr) (observed.2.2.2.2.2.2 h gr)
      ((raw) h gr) axis))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
