import OAI.Hierarchy.DescentNamedOriginalEarnedSites
import OAI.Hierarchy.DescentChosenExteriorHeadWidths
import OAI.Hierarchy.DescentOriginalInitialParameters
import OAI.Hierarchy.DescentOriginalFundedStageHost
import OAI.Hierarchy.DescentOriginalFundedSeed
import OAI.Hierarchy.DescentFixedHostPlacement
import OAI.Hierarchy.DescentOriginalFinalEventPlacement
import OAI.Hierarchy.DescentFixedStageReturns
import OAI.Hierarchy.DescentTerminalHostISARoom

namespace OAI
/-! # A host on the single purchased, dyadic original memory -/
namespace Hierarchy.DescentSixParty.SeedNamed
section
open Lean Meta Elab Command Term
set_option maxHeartbeats 3500000
set_option maxRecDepth 25000
private theorem reassociateBuyerPrice (amount price copies capacity : Nat)
    (receipt : amount ≤ price*(copies*capacity)) : amount ≤ price*copies*capacity := by
  simpa only [Nat.mul_assoc] using receipt

private def priceOperands (operation : Name) (term : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let atom := term.consumeMData
  let args := atom.getAppArgs
  unless atom.isAppOf operation && args.size ≥ 2 do
    throwError "expected {operation}, found {atom.getAppFn} in the original stage invoice"
  return (args[args.size-2]!, args[args.size-1]!)

run_cmd liftTermElabM do
  let donor ← getConstInfo ``original_funded_invoice_from_purchase
  let levels := donor.levelParams.map Level.param
  let (type, value) ← forallTelescope donor.type fun xs purchaseProposition => do
    let (amount, rhs) ← priceOperands ``LE.le purchaseProposition
    let (price, volume) ← priceOperands ``HMul.hMul rhs
    let (copies, capacity) ← priceOperands ``HMul.hMul volume
    let receipt := mkAppN (mkConst donor.name levels) xs
    let proof := mkAppN (mkConst ``reassociateBuyerPrice) #[amount,price,copies,capacity,receipt]
    let conclusion ← inferType proof
    return (← mkForallFVars xs conclusion, ← mkLambdaFVars xs proof)
  let name := mkPrivateName (← getEnv) `OAI.Hierarchy.DescentSixParty.SeedNamed.grid_original_bought_price
  addDecl <| .thmDecl {name, levelParams:=donor.levelParams, type, value}

run_cmd liftTermElabM do
  let donor ← getConstInfo ``original_replay_word
  let levels := donor.levelParams.map Level.param
  let (type, value) ← forallTelescope donor.type fun xs both => do
    let atom ← whnf both
    unless atom.isAppOfArity ``And 2 do throwError "word receipt should have two parts"
    let pair := mkAppN (mkConst donor.name levels) xs
    let proof := mkAppN (mkConst ``And.right) (atom.getAppArgs.push pair)
    let target := atom.getAppArgs[1]!
    return (← mkForallFVars xs target, ← mkLambdaFVars xs proof)
  let name := mkPrivateName (← getEnv) `OAI.Hierarchy.DescentSixParty.SeedNamed.grid_original_terminal_word_fit
  addDecl <| .thmDecl {name,levelParams:=donor.levelParams,type,value}
end

end Hierarchy.DescentSixParty.SeedNamed

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentMixedRouter Catalyst DescentInitialHost DescentExteriorReplay
open DescentTerminalPreflightSpace DescentTerminalFixedSlices DescentTerminalPrimitiveArena
open DescentTerminalPointerDigits DescentTerminalCombinedRole DescentSIMDLookup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ThreeFlat.Routing CallPool
open scoped Classical
open DescentSIMDLookup DescentPackedColony DescentColonies DescentTerminalLocalPortBook DescentTerminalGraphPositions
open DescentTerminalSiteShelves DescentTerminalVertexFields DescentTerminalPointerIssue
open DescentTerminalRoleTables DescentTerminalCombinedRole DescentSortedRoster DescentActorRaster
open DescentColonies.SplitRAM
open scoped Fin.CommRing
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentResetInvoice CorrectionBatch
open DescentSixParty.SeedNamed.Branch DescentRotor
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F)
variable (epoch₀ : AtomSchedule) (pitch₀ rate₀ batch₀ frozen₀ grain₀ drift₀ : ℕ)
    (rotor₀ : RotorSpec) (rows₀ paid₀ : ℕ) (base₀ : epoch₀.baseGroups = 2^frozen₀) (bin₀ : epoch₀.radix = 2^pitch₀)
    (phase₀ : DescentTerminalFixedSlices.Phase F) (eq₀ : 2^pitch₀ = phase₀.output.receiver.blocks)
    (floor₀ roles₀ matrix₀ census₀ : ℕ)
local notation "spec₀" => Branch.preflightSpec X G epoch₀ pitch₀ rate₀ batch₀ frozen₀
  (Branch.geometryFormat G epoch₀ pitch₀ rate₀ batch₀ frozen₀ grain₀ drift₀ rotor₀ rows₀ paid₀)
local notation "nodes₀" => epoch₀.epochPower^epoch₀.localTokenExponent
local notation "args₀" => NativeBranch.privateSlotCapacity G epoch₀ drift₀
local notation "dateHardware" => (phase₀.output).receiver
local notation "dateBlocks" => (spec₀).scalar.blocks
local notation "blockCast" => (eq₀ : dateBlocks=(dateHardware).blocks)
local notation "paidBank" => fun x:Fin dateBlocks=>(phase₀.output).terminalPaid phase₀.dateBase x.val
local notation "actorBank" => fun x:Fin dateBlocks=>(phase₀.output).terminalActor phase₀.dateBase x.val
local notation "wingBank" => fun (x:Fin dateBlocks) (a:Fin (2*(spec₀).cap))=>(phase₀.output).terminalWing phase₀.dateBase x.val a.val
local notation "peerBank" => (phase₀.output).terminalPeer phase₀.dateBase
local notation "dateColors" => DescentPrimitivePalette.colors G (epoch₀.firstWidth G.b batch₀) (epoch₀.grainAt G.b batch₀ 0) rotor₀
local notation "roleBankBits" => fun roleField:Fin 6=>DescentTerminalCombinedRole.width dateColors (max 8 (2^(epoch₀).capGain))
  args₀ batch₀ drift₀ roleField*((epoch₀).epochPower^(epoch₀).localTokenExponent)*(spec₀).groups
local notation "atomBits" => Nat.clog 2 (nodes₀+1)
local notation "operandWidths" => (⟨atomBits,Nat.clog 2 (args₀+1),fun _=>DescentOperandWidth.recordBits G epoch₀ pitch₀ frozen₀ drift₀ 3 batch₀,some nodes₀⟩:Widths)
local notation "terminalPin" => DescentExterior.terminalPin ((epoch₀).groupWidth pitch₀ frozen₀ 0+pitch₀) ((epoch₀).groupWidth pitch₀ frozen₀ (epoch₀).length+pitch₀) (pitch₀*(epoch₀).length)
local notation "publicCell" => DescentTerminalPointerDigits.publicCell («cap»:=(spec₀).cap) (N:=nodes₀) (A:=args₀)
  (d:=(spec₀).scalar.pointerBits) 3 grain₀ G.b (poolBatchCount ((epoch₀.firstWidth G.b batch₀)*1) batch₀) (pitch₀*(epoch₀).length) (spec₀).groups operandWidths
local notation "privateCell" => DescentTerminalPointerDigits.output (spec₀).cap nodes₀ args₀ 3 (spec₀).groups
  (spec₀).scalar.pointerBits (Nat.clog 2 (grain₀+args₀+1)) grain₀ G.b (poolBatchCount ((epoch₀.firstWidth G.b batch₀)*1) batch₀) operandWidths terminalPin
local notation "roleBanks" => DescentTerminalRoleTables.role roleBankBits ((phase₀).banks floor₀) roles₀
local notation "arityBanks" => DescentTerminalRoleTables.arity roleBankBits ((phase₀).banks floor₀) roles₀
local notation "pointerBank" => fun (pointerField:Fin 4) (slot:Fin (phase₀.output).argumentSlots) (block:Fin dateBlocks) =>
  (phase₀.output).terminalPointers phase₀.dateBase pointerField slot (block.cast blockCast)
local notation "oldOperands" => DescentTerminalOperandRepack.padded («K»:=args₀) pointerBank paidBank
local notation "operandChart" => ((spec₀).pointerPages census₀ matrix₀ oldOperands wingBank).address (N:=nodes₀)
local notation "decoder₀" => Branch.decodeBook epoch₀ G base₀ bin₀ batch₀ grain₀ 3
  (spec₀).cap (spec₀).printBits (by decide)

private def acquiredGeometryBooks (word₀ : ℕ) (source₀ : Memory word₀) : Memory word₀ :=
  (spec₀).bookSnapshot (base:=census₀) (peer:=peerBank) (wing:=wingBank)
    (w:=word₀) (q:=grain₀) (p:=batch₀) (nd:=atomBits) (nodes:=nodes₀) (hidden:=args₀) (args:=args₀)
    (oldPaid:=paidBank) (actor:=actorBank) (first:=roleBanks) (second:=arityBanks) (chart:=operandChart)
    (f0:=publicCell) (f7:=privateCell) (decode:=decoder₀) source₀

end
end Hierarchy.DescentSixParty.SeedNamed

namespace Hierarchy.DescentSixParty.SeedNamed
open Lean Meta Elab Term in
local elab "physicalHeadRoom% " boundArg:term:arg " using " equalityArg:term:arg : term => do
  let bound ← withSynthesize (postpone := .no) <| elabTerm boundArg none
  let agreement ← withSynthesize (postpone := .no) <| elabTerm equalityArg none
  let boundType := (← inferType bound).consumeMData
  unless boundType.isAppOfArity ``LT.lt 4 do
    throwError "expected the physical header comparison; got {boundType.getAppFn}"
  let family ← withLocalDeclD `censusAddress (mkConst ``Nat) fun address => do
    mkLambdaFVars #[address] (mkAppN boundType.getAppFn (boundType.getAppArgs.set! 3 address))
  mkEqMP (← mkCongrArg family (← mkEqSymm agreement)) bound

open Lean Meta Elab Term in
local elab "physicalLiteralRoom% " paid:term:arg " using " alignment:term:arg : term => do
  let proof₀ ← withSynthesize (postpone := .no) <| elabTerm paid none
  let same₀ ← withSynthesize (postpone := .no) <| elabTerm alignment none
  let held := (← inferType proof₀).consumeMData
  unless held.isAppOfArity ``LE.le 4 do
    throwError "expected purchased ROM upper bound; got {held.getAppFn}"
  let right := held.appArg!.consumeMData
  unless right.isAppOfArity ``DescentTerminalPreflightSpace.Spec.literalBase 2 do
    throwError "expected the literal shelf; got {right.getAppFn} on {right.getAppNumArgs} arguments"
  let family ← withLocalDeclD `address₀ (mkConst ``Nat) fun base₀ => do
    let shelf₀ := mkAppN right.getAppFn (right.getAppArgs.set! 1 base₀)
    mkLambdaFVars #[base₀] (mkAppN held.getAppFn (held.getAppArgs.set! 3 shelf₀))
  let moved ← mkCongrArg family (← mkEqSymm same₀)
  mkEqMP moved proof₀

open Lean Meta Elab Term in
private def purchasedStageInvoiceFields (op : Name) (term : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let mut atom := (← instantiateMVars term).consumeMData
  for _ in [:32] do
    match atom with
    | .letE _ _ exprValueTag remainder _ => atom := (remainder.instantiate1 exprValueTag).consumeMData
    | _ => break
  let args := atom.getAppArgs
  unless atom.isAppOf op && args.size ≥ 2 do
    throwError "expected {op}, found {atom.getAppFn} in the original stage invoice"
  return (args[args.size-2]!,args[args.size-1]!)

open Lean Meta Elab Term in
local elab "actualPaidBounds% " allowance:term "," invoice:term "," ratio:term : term => do
  let supplied ← withSynthesize (postpone := .no) <| elabTerm allowance none
  let paid ← withSynthesize (postpone := .no) <| elabTerm invoice none
  let multiple ← withSynthesize (postpone := .no) <| elabTerm ratio none
  let (lhs, _) ← purchasedStageInvoiceFields ``LE.le (← inferType paid)
  let (charged, _) ← purchasedStageInvoiceFields ``HMul.hMul lhs
  let (extra, timed) ← purchasedStageInvoiceFields ``HAdd.hAdd charged
  let (scaled, _) ← purchasedStageInvoiceFields ``HMul.hMul timed
  let (_, physical) ← purchasedStageInvoiceFields ``HMul.hMul scaled
  let (withPayload, _) ← purchasedStageInvoiceFields ``HAdd.hAdd physical
  let (withOutput, _) ← purchasedStageInvoiceFields ``HAdd.hAdd withPayload
  let (withTime, outputs) ← purchasedStageInvoiceFields ``HAdd.hAdd withOutput
  let (withMemory, clock) ← purchasedStageInvoiceFields ``HAdd.hAdd withTime
  let (withRegs, firstFree) ← purchasedStageInvoiceFields ``HAdd.hAdd withMemory
  let (pcs, regs) ← purchasedStageInvoiceFields ``HAdd.hAdd withRegs
  return mkAppN supplied #[pcs,regs,firstFree,clock,outputs,extra,multiple,paid]

open Lean Meta Elab Term in
private def exposePurchaseHead (expected : String) (e : Lean.Expr) : MetaM Lean.Expr := do
  let mut curr := e.consumeMData
  for _ in [:20] do
    if let .const (.str _ label) _ := curr.getAppFn then
      if label == expected then return curr
    if let .letE _ _ val tail _ := curr then
      curr := (tail.instantiate1 val).consumeMData
    else
      let some inner ← unfoldDefinition? curr | throwError "could not expose {expected} from {curr.getAppFn}"
      curr := inner.consumeMData
  throwError "failed to expose {expected} from {e.getAppFn}"

open Lean Meta Elab Term in
private def findReadoutSpine (prop : Lean.Expr) : MetaM (Array (Lean.Expr × Nat) × Lean.Expr) := do
  let mut curr := prop
  let mut spine := #[]
  for (label, numFromEnd) in [("lt",2),("hAdd",2),("trailingStop",4),("trailingCut",2),("last",1),("maskBase",1)] do
    let form ← exposePurchaseHead label curr
    let vals := form.getAppArgs
    let k := vals.size-numFromEnd
    spine := spine.push (form,k)
    curr := vals[k]!
  return (spine,curr)

open Lean Meta Elab Term in
local elab "paidWordAtPhysicalScan% " bound:term:arg agreement:term:arg : term => do
  let oldWord ← Term.elabTerm bound none
  let scanAgreement ← Term.elabTerm agreement none
  let (arithmeticContexts, _) ← findReadoutSpine (←inferType oldWord)
  let readoutAt ← withLocalDeclD `scanValue (mkConst ``Nat) fun z => do
    let mut expression := z
    for (enclosingNode, operandNumber) in arithmeticContexts.reverse do
      expression := mkAppN enclosingNode.getAppFn (enclosingNode.getAppArgs.set! operandNumber expression)
    mkLambdaFVars #[z] expression
  let relabelled ← mkCongrArg readoutAt (←mkEqSymm scanAgreement)
  mkEqMP relabelled oldWord

private theorem purchasedWordAddressFits {address lastRate height wordBits : Nat}
    (measured : address ≤ 2^(lastRate*height)) (bought : (2*lastRate+7)*height ≤ wordBits)
    (large : 4 ≤ height) : address < 2^wordBits :=
  measured.trans_lt (Nat.pow_lt_pow_right (by decide : 1 < 2)
    ((Nat.mul_lt_mul_of_pos_right (by omega : lastRate < 2*lastRate+7)
      (Nat.lt_of_lt_of_le (by decide : 0 < 4) large)).trans_le bought))

open Lean Meta Elab Term in
private def purchasedActualPaidArea (measured fundingFits height scanAgreement : Lean.Expr) : TermElabM Lean.Expr := do
  let bounded ← mkAppM ``purchasedWordAddressFits #[measured, fundingFits, height]
  let boundType ← inferType bounded
  unless boundType.getAppFn.isConstOf ``LT.lt && boundType.getAppNumArgs == 4 do
    throwError "expected the purchased word address bound"
  let readout := boundType.getAppArgs[2]!.consumeMData
  unless readout.getAppFn.isConstOf ``DescentTerminalCompiledPrefix.AddressPlan.last && readout.getAppNumArgs == 6 do
    throwError "expected the purchased terminal readout"
  let mask := readout.getAppArgs.back!.consumeMData
  unless mask.getAppFn.isConstOf ``DescentTerminalPreflightSpace.Spec.maskBase && mask.getAppNumArgs == 2 do
    throwError "expected the purchased terminal mask start"
  let predicate ← withLocalDeclD `scanBase (mkConst ``Nat) fun replacement => do
    let newAddress := mkApp readout.appFn! (mkApp mask.appFn! replacement)
    mkLambdaFVars #[replacement] (mkAppN boundType.getAppFn (boundType.getAppArgs.set! 2 newAddress))
  mkEqMP (← mkCongrArg predicate (← mkEqSymm scanAgreement)) bounded

open Lean Elab Term in
local elab "originalPaidAreaAtCensus% " measured:term:arg fundingFits:term:arg height:term:arg
    agreement:term:arg : term => do
  purchasedActualPaidArea (← elabTerm measured none) (← elabTerm fundingFits none)
    (← elabTerm height none) (← elabTerm agreement none)

open Lean Elab Meta Term Command in
private def earnedBinderNames : Lean.Expr → Array Name
  | .forallE n _ other _ => #[n] ++ earnedBinderNames other
  | _ => #[]
open Lean Elab Meta Term Command in
private def originalEarnedAtPage {α : Type} [Inhabited α] (g : Lean.Expr) (witnesses : Array α)
    (readWitness : α → Lean.Expr → TermElabM Lean.Expr) : TermElabM Lean.Expr := do
  let donor ← getConstInfo ``original_earned_sites_of_words_at_height
  let publicPage ← getConstInfo ``WideEarnedSitePages
  let mut target := (← instantiateMVars g).consumeMData
  for _ in [:16] do
    if target.getAppFn.isConstOf publicPage.name then break
    let some next ← withTransparency .all <| unfoldDefinition? target | throwError "expected a purchased earned site page, saw {target.getAppFn.constName?}"
    target := next.headBeta.consumeMData
  unless target.getAppFn.isConstOf publicPage.name do throwError "unrecognized purchased page"
  let publicNames := earnedBinderNames publicPage.type
  let publicArgs := target.getAppArgs
  let need := earnedBinderNames donor.type
  let operator := Lean.mkConst donor.name target.getAppFn.constLevels!
  let mut inputs := #[]
  let mut ix := 0
  for name in need do
    let aligned := if name == `wideShort then `short else name
    let located := if name.toString.startsWith "inst." then 1 else publicNames.idxOf aligned
    if located < publicArgs.size then
      inputs := inputs.push publicArgs[located]!
    else
      unless ix < witnesses.size do throwError "missing concrete earned field {name}"
      let applied := mkAppN operator inputs
      let physical ← whnf (← inferType applied)
      unless physical.isForall do throwError "expected original paid binder {name}"
      inputs := inputs.push (← readWitness (witnesses[ix]!) physical.bindingDomain!)
      ix := ix + 1
  unless ix == witnesses.size do throwError "unexpected physical field count {ix}/{witnesses.size}"
  return mkAppN operator inputs
open Lean Elab Meta Term Command in
local elab "purchasedEarnedOnPage% " "[" args:term,* "]" : term <= g => do
  originalEarnedAtPage g args.getElems (fun a t => withoutErrToSorry <| elabTerm a (some t))

open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalGraphPositions DescentTerminalGraphVolume DescentTerminalCableOrder DescentKernelHistory
open DescentBundleHistory DescentPrimitivePalette DescentRotor DescentResetGates CorrectionBatch
open DescentTerminalBinReaddress DescentTerminalPorts Computability.BorderVNP.Crossing
open DescentTerminalEmitter DescentTerminalEmitter.Branch DescentTerminalChipRuntime
open DescentTerminalVertexFields DescentTerminalHeaderScatter DescentTerminalSiteShelves
open DescentTerminalScalarTransposes DescentTerminalDenseWindow DescentTerminalRecipeRows
open DescentTerminalScalarPadded DescentTerminalCompiledPrefix DescentEpochTagKeys
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical BigOperators
open DescentTerminalHost DescentTerminalThreshold DescentTerminalLast DescentTerminalRAM
open DescentTerminalReadout DescentTerminalFixedISAHost CorrectionFrame DescentTerminalChipPins
open ThreeFlat Routing Diagonal TraceBanks
open Computability.VPVNP.RAMMemory TaggedShorterControlHistory Tagged Tagged.SortLift TaggedShorterHistoryOrder
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option cleanup.letToHave false
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin Branch.archive Branch.bundleShape

section
open Chronology
private def purchasedRoleLiteralImage {F : Type} [Field F] (G : PoweredGadget F) (op : RotorSpec)
    (epoch : AtomSchedule) (grainSize drift baseAddr : ℕ) {width : ℕ}
    (input : Computability.VPVNP.BurstRAM.Memory width) : Computability.VPVNP.BurstRAM.Memory width :=
  let pitch := epoch.firstWidth G.b grainSize
  let tokens := epoch.grainAt G.b grainSize 0
  let hidden := NativeBranch.privateSlotCapacity G epoch drift
  let literalWords : ℕ → ℕ := DescentTerminalRoleTables.literal
    (n := DescentPrimitivePalette.colors G pitch tokens op)
    (A := max 8 (2^epoch.capGain)) (G := hidden) (p := grainSize) (R := drift)
    (N := epoch.epochPower^epoch.localTokenExponent) (groups := epoch.groupCount epoch.length)
    (DescentPrimitivePalette.codec (G := G) (s := pitch) (Z := tokens) op) hidden
  DescentStaticWordColumn.image (w := width) baseAddr literalWords input
    (DescentTerminalRoleTables.count (originalRoleBits G op epoch grainSize drift))

private theorem purchasedRoleLiteralImage_eq {F : Type} [Field F] (G : PoweredGadget F) (op : RotorSpec)
    (epoch : AtomSchedule) (grainSize drift baseAddr roof : ℕ) {width : ℕ}
    (endAt : baseAddr + DescentTerminalRoleTables.count (originalRoleBits G op epoch grainSize drift) ≤ roof)
    (fits : roof < 2^width) (input : Computability.VPVNP.BurstRAM.Memory width) :
    purchasedRoleLiteralImage G op epoch grainSize drift baseAddr input =
      (originalRoleMount G op epoch grainSize drift baseAddr roof endAt fits).phase.image input := rfl


private def purchasedEndCapture {width : ℕ} (control : ℕ → DateCode width)
    (sourceRAM : Computability.VPVNP.BurstRAM.Memory width) (lastTick first : ℕ)
    (selectAt : ℕ → ℕ) (calendar : List ℕ) : Computability.VPVNP.BurstRAM.Memory width :=
  let lastImage := DateCode.history (w := width) control sourceRAM lastTick
  DescentLowCountBook.output (w := width) first (fun pos => selectAt ((calendar)[pos]?.getD 0))
    lastImage calendar.length

end

open Lean Elab Term in
local elab "conjunctionPort% " t:term:arg i:num n:num : term => do
  let mut e ← elabTerm t none
  let idx := i.getNat
  let count := n.getNat
  unless idx < count do throwError "invalid physical conjunction position"
  for _ in [:idx] do e := mkProj ``And 1 e
  return if idx + 1 < count then mkProj ``And 0 e else e


private theorem purchasedDyadicHeight {h : ℕ} (dyadic : ∃ a, h = 2^a) :
    h = DescentDyadicSpan.span h := by
  obtain ⟨a, rfl⟩ := dyadic
  unfold DescentDyadicSpan.span
  rw [Nat.clog_pow 2 a (by decide)]


private theorem purchasedWidthStrict {last height width : Nat} (positive : 0 < height)
    (bought : (2 * last + 7) * height ≤ width) : last * height < width :=
  Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (by omega : last < 2 * last + 7) positive) bought

private theorem purchasedInputRoom {height width : Nat} (large : 4 ≤ height)
    (received : 3 * height ≤ width) : height + 1 ≤ width := by omega

private theorem purchasedPackedWidth {packed height width : Nat}
    (room : 16 * packed ≤ height) (embed : height ≤ width) : packed ≤ width := by omega

private theorem purchasedMachineWidth {bins sockets piece height width : Nat}
    (room : 16 * (sockets * (bins * piece)) ≤ height) (embed : height ≤ width) :
    (bins * sockets) * piece ≤ width := by
  simpa only [Nat.mul_comm bins sockets, Nat.mul_assoc] using purchasedPackedWidth room embed

/-- Evaluate a binder type at the purchased stage, its group exponent, and its frozen tail. -/
abbrev AtPurchasedStage.{v} {F : Type} [Field F] (G : PoweredGadget F)
    (rounds f g restart τ β siteCount payloadBits : ℕ)
    (family : AtomSchedule → ℕ → ℕ → Sort v) : Sort v :=
  let depth := Nat.log 2 payloadBits / (2 * β)
  let frozen := DescentCompiler.TerminalScale.tail τ depth
  let epoch := stageNumbers G rounds depth f g restart siteCount frozen
  let pitch := groupBits rounds depth epoch.hostGain epoch.capGain (cutRate rounds f g)
  family epoch pitch frozen

variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F)
variable {n h C f g : ℕ} (rounds restart τ β siteCount payloadBits : ℕ)
variable (opened:10*(X.size+1)≤ siteCount) (smaller:siteCount≤(2^payloadBits)^2)
  (low:2^payloadBits≤ siteCount) (dyadic:∃a,siteCount=2^a)
local notation "cut" => cutRate rounds f g
local notation "src_" => (⟨cp,P,siteCount,X,opened,smaller⟩:ShellSource F payloadBits)
local notation "depth_" => Nat.log 2 payloadBits/(2*β)
local notation "tail" => DescentCompiler.TerminalScale.tail τ depth_
local notation "S" => stageNumbers G rounds depth_ f g restart siteCount tail
local notation "k" => groupBits rounds depth_ (hostRate rounds restart) (capRate G rounds g) (cutRate rounds f g)
local notation "W" => NativeBranch.binLimit («k»:=k) S
local notation "j" => Nat.clog 2 (NativeBranch.localLimit G S)
local notation "q" => 2^j*(G.b^(rounds*depth_)*G.b)
local notation "piece" => payloadBits/(16*(q*W))
local notation "rest" => (S).groupWidth k tail 0+k-2*j
local notation "p" => W*piece
variable (ordinary : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch pitch _ => OrdinaryRates G epoch pitch (cutRate rounds f g)))
  (reset : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch pitch frozen => ResetRates G epoch pitch (atRound epoch.rounds) n h C f g (cutRate rounds f g) frozen))
variable (branch : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch _ _ => G.b ≤ 2^epoch.capGain))
  (positive : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch pitch _ => 0 < headGrain G epoch pitch payloadBits))
  (room : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch _ _ => 10*(X.size+1) ≤ epoch.initialSites))
variable (shorten : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch _ _ => reentryRate h C*(1-(2-G.rate)/4)^epoch.rounds ≤ 1/2))
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "last" => Epochs.finish G _ _ (cert).choose
local notation "s" => (S).firstWidth G.b p
local notation "Z" => (S).grainAt G.b p 0
local notation "rot" => RotorSpec.ofRates reset
local notation "R" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "cap" => NativeBranch.privateSlotCapacity G S R
local notation "nodeCap" => (S).epochPower^(S).localTokenExponent
local notation "venues" => (S).groupCount (S).length*2^k

variable (base : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch _ frozen => epoch.baseGroups = 2^frozen))
  (width : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch pitch frozen => epoch.groupWidth pitch frozen 0 + pitch =
      headChunk G epoch + (headChunk G epoch + headRest G epoch pitch frozen)))
variable (age : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch _ _ => 0 < epoch.height))
  (wFit : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch pitch _ =>
      let split := NativeBranch.binLimit («k»:=pitch) epoch
      split ≤ split))
  (qFit : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch _ _ => NativeBranch.localLimit G epoch ≤
      2^(headChunk G epoch)*(G.b^(epoch.rounds*epoch.height)*G.b)))
  (qh : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch _ _ => 0 < 2^(headChunk G epoch)*(G.b^(epoch.rounds*epoch.height)*G.b)))

open DescentExterior Computability.VPVNP.RAMSerialization DescentTerminalExteriorPackets DescentTerminalPublicIdentity
open DescentTerminalDenseGraphRead DescentTerminalDenseWindow
open DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall DescentPackedProfileTape
open DescentSeedRoot DescentExteriorShelf DescentTerminalPrimitiveArena
local notation "E₀" => Fintype.card (Port P X.width)
local notation "H₀" => (S).hostSize (S).length
local notation "count₀" => E₀*2^(j+rest)
variable (sitesPositive : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch _ _ => 0 < epoch.hostSize epoch.length))
local notation "sitePos_" => (lt_of_lt_of_le (Nat.two_pow_pos payloadBits) low)
local notation "template" => shellTemplate X G rounds depth_ f g restart siteCount τ payloadBits n h C sitePos_
local notation "rawWords" => terminalRawRows X G S p q n h C f g
local notation "headerRows" => terminalPool X G S p q W n h C f g
local notation "paidRows" => headerRows
local notation "cfg" => Branch.exteriorShape template E₀ j rest s rawWords headerRows H₀ sitesPositive
local notation "shape_" => original_shell_fields X G rounds depth_ f g restart siteCount τ payloadBits n h C sitePos_
local notation "pool" => (shape_).1
local notation "raw" => (shape_).2.1
local notation "groupsAt" => (S).groupCount (S).length
open DescentTerminalCompiledPrefix.AddressPlan DescentTerminalEmitter.Compact
open DescentTerminalLocalPortBook DescentTerminalSpanBook DescentTerminalBinPack
open DescentTerminalPreflightSpace ThreeFlat.RAM PhysicalProcedure

open DescentPackedEpochFold DescentExteriorMatrixUpdate DescentPackedSeed DescentSeedRoot
open ThreeFlat Routing Diagonal
variable (ratio₀:ℕ)
local notation "w" => ratio₀*payloadBits
variable (fit : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch pitch _ => epoch.firstWidth G.b (headGrain G epoch pitch payloadBits) < 2^(ratio₀*payloadBits)))
local notation "K" => calibratedBins X G rounds depth_ f g restart siteCount τ payloadBits n h C
local notation "chart" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
local instance purchasedStageChartFinite : Fintype (chart).Pin := (chart).finite
local notation "fmt" => Branch.geometryFormat G S k g p tail q R rot headerRows paidRows
local notation "pre" => Branch.preflightSpec X G S k g p tail ({fmt with binSize:=W}:Branch.PreflightFormat)
local notation "steps" => (chart).layout
local notation "lo" => DescentWideSeedFlags.selectorBase X (S).copies s payloadBits (steps).length
local notation "packWidth" => DescentPackedEpochShelves.grain (payloadBits/2) G.C
local notation "matrixAt" => end_ (lo+extent packWidth steps) G.C packWidth
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentResetInvoice CorrectionBatch
open DescentSixParty.SeedNamed.Branch DescentExteriorReplay DescentTerminalFixedSlices
open DescentTerminalPointerDigits DescentTerminalCombinedRole DescentSIMDLookup DescentPackedColony
open ThreeFlat.Routing CallPool DescentColonies DescentActorRaster DescentColonies.SplitRAM
open DescentTerminalRoleTables DescentTerminalPointerIssue
open Chronology DescentDatedSeedStartup.Input DescentTerminalEpochDecoder
variable (headRate_ datesRate_ codeRate_ lastRate_ slots_:ℕ)
local notation "dateDegree" => maximumDegree (rounds+1)
local notation "board" => reset.board
local notation "bootHosts" => siteCount
local notation "seedWire_" => (S).epochPower^(S).priceExponent
local notation "seedHist_" => s
local notation "vhead_" => originalSeedHead G rot R X steps S k tail payloadBits bootHosts dateDegree seedWire_ seedHist_
  (terminalBinCount X G S p q W n h C f g+1) rawWords
local notation "startup" => (vhead_).layout G rounds f g R payloadBits
local notation "startingHeader" => (vhead_).base G payloadBits-1
variable (funding :
  let historySize := max 1 (max reset.bitsR (C*reset.bitsR))
  OriginalWord G reset.board (RotorSpec.ofRates reset) rounds f g restart (cutRate rounds f g)
    historySize (maximumDegree (rounds+1)) branch headRate_ datesRate_ codeRate_ lastRate_
    ratio₀ τ β payloadBits (historySize+1) slots_)
local notation "heads_" => original_funded_seed G board rot rounds f g restart cut R dateDegree τ β payloadBits src_ branch
  headRate_ datesRate_ codeRate_ lastRate_ ratio₀ slots_ ordinary reset positive shorten fit siteCount
  dateDegree seedWire_ seedHist_ funding low dyadic le_rfl (Nat.le_pow_clog (by decide : 1<2) siteCount)
local notation "hostsEnough" => (heads_).hosts
local notation "primitiveLanes_" => DescentDatedSeedStartup.Primitive.paletteLanes G rot (startup).seedWidth Z payloadBits k
local notation "initialSource_" => DescentPackedSeed.Primitive.Source.jobs X (S).copies (startup).seedWidth payloadBits
local notation "seedEnd_" => (DescentDatedSeedStartup.Input.nodeChart startup k bootHosts ((S).groupCount 0)).seedEnd
  (DescentDatedSeedStartup.endAddress X startup bootHosts ((S).groupCount 0) k)
local notation "initialBound_" => DescentDatedSeedStartup.Primitive.initialEnd X (S).copies (startup).seedWidth payloadBits k
  bootHosts ((S).groupCount 0) primitiveLanes_ seedEnd_

local notation "entry_" => (⟨DatePorts.initial G rot X (S).copies startup k bootHosts ((S).groupCount 0) payloadBits Z,
    initialBound_⟩ : RegisterTimeline.Position)
local notation "traces_" => traceAt X G S ordinary reset branch positive room shorten
local notation "menu_" => RegisterTimeline.fromProfiles G S board rot k tail p f g R dateDegree payloadBits lo startingHeader steps
local notation "cursor_" => RegisterTimeline.calendar («w»:=w) traces_ menu_ entry_
local notation "datesAt" => RunTrace.machine traces_ (fun i _=>RegisterTimeline.instruction («w»:=w) traces_ menu_ entry_ i)
local notation "dateAge" => (S).length-1
local notation "prior_" => cursor_ dateAge
local notation "ordinaryAt" => (menu_).ordinary
local notation "datePayload" => payloadBits
local notation "operandLanes" => (prior_).ports.operandLanes
local notation "primitiveLanes" => (prior_).ports.roleLanes
local notation "previousDate" => (prior_).ports.venue
local notation "priorAddress" => (prior_).ports.io.wire
local notation "rosterBank" => (prior_).ports.io.roster
local notation "datedFloor" => (prior_).ports.priorStart k (prior_).floor
local notation "dateTag" => RegisterTimeline.Menu.resetFlag S
local notation "dateRotation" => fun i=>(menu_).rotationAt G S k i (cursor_ i)
local notation "countAt" => fun i=>(menu_).selectorAt G S k i (cursor_ i)
local notation "rankDir_" => RegisterTimeline.snapshotDirectory («w»:=w) traces_ menu_ entry_
local notation "snapshots" => SnapshotCalendar reset (kindCalendar (S).rounds (S).height)
  (capCalendar G.b (S).rounds g (S).height) rankDir_
local notation "rankFloor" => (cursor_ (S).length).floor
local notation "roleBase" => max rankFloor (matrixAt+32*DescentExteriorShelf.span j rest s E₀)
local notation "replayBase" => roleBase+DescentTerminalRoleTables.count (originalRoleBits G rot S p R)

local notation "dateSpec" => preflightSpec X G S k g p tail (geometryFormat G S k g p tail q R rot headerRows paidRows)
local notation "datePorts" => Fintype.card (Port P X.width)
local notation "datePhase" => Phase.scheduled G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot
  operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor
local notation "dateOut" => (datePhase).output
local notation "dateOrigin" => (datePhase).dateBase
local notation "dateMachine" => PhysicalReset.scheduled G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot
  s Z operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor
local notation "dateCalendar" => replayCalendar X S k tail j rest snapshots
local notation "earlyFloor" => DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail replayBase j rest s datePorts
local notation "earlyImage" => DescentExteriorMatrixUpdate.Calendar.earlyImage S k tail replayBase dateTag dateRotation j rest s datePorts matrixAt
local notation "sliceEnd" => (datePhase).stop earlyFloor
local notation "lookupBase" => (dateCalendar).packetEnd sliceEnd
local notation "lookupPage" => (dateSpec).scanPages lookupBase q
local notation "censusBase" => (lookupPage).stop
local notation "dateHardware" => (dateOut).receiver
local notation "dateBlocks" => (dateSpec).scalar.blocks
local notation "blockCast" => (rfl : dateBlocks=(dateHardware).blocks)
local notation "paidBank" => fun x:Fin dateBlocks=>(dateOut).terminalPaid dateOrigin x.val
local notation "actorBank" => fun x:Fin dateBlocks=>(dateOut).terminalActor dateOrigin x.val
local notation "wingBank" => fun (x:Fin dateBlocks) (a:Fin (2*(dateSpec).cap))=>(dateOut).terminalWing dateOrigin x.val a.val
local notation "peerBank" => (dateOut).terminalPeer dateOrigin
local notation "dateColors" => DescentPrimitivePalette.colors G s Z rot
local notation "roleBankBits" => fun roleField:Fin 6=>DescentTerminalCombinedRole.width dateColors (max 8 (2^(S).capGain))
  cap p R roleField*((S).epochPower^(S).localTokenExponent)*(dateSpec).groups
local notation "atomBits" => Nat.clog 2 (nodeCap+1)
local notation "operandWidths" => (⟨atomBits,Nat.clog 2 (cap+1),fun _=>DescentOperandWidth.recordBits G S k tail R 3 p,some nodeCap⟩:Widths)
local notation "terminalPin" => DescentExterior.terminalPin ((S).groupWidth k tail 0+k) ((S).groupWidth k tail (S).length+k) (k*(S).length)
local notation "publicCell" => DescentTerminalPointerDigits.publicCell («cap»:=(dateSpec).cap) (N:=nodeCap) (A:=cap)
  (d:=(dateSpec).scalar.pointerBits) 3 q G.b (poolBatchCount (s*1) p) (k*(S).length) (dateSpec).groups operandWidths
local notation "privateCell" => DescentTerminalPointerDigits.output (dateSpec).cap nodeCap cap 3 (dateSpec).groups
  (dateSpec).scalar.pointerBits (Nat.clog 2 (q+cap+1)) q G.b (poolBatchCount (s*1) p) operandWidths terminalPin
local notation "roleBanks" => DescentTerminalRoleTables.role roleBankBits ((datePhase).banks earlyFloor) roleBase
local notation "arityBanks" => DescentTerminalRoleTables.arity roleBankBits ((datePhase).banks earlyFloor) roleBase
local notation "matrixFloor" => DescentExteriorMatrixUpdate.Calendar.stop S k tail replayBase+(S).length
local notation "pointerBank" => fun (pointerField:Fin 4) (slot:Fin (dateOut).argumentSlots) (block:Fin dateBlocks) =>
  (dateOut).terminalPointers dateOrigin pointerField slot (block.cast blockCast)
local notation "oldOperands" => DescentTerminalOperandRepack.padded («K»:=cap) pointerBank paidBank
local notation "operandChart" => ((dateSpec).pointerPages censusBase matrixFloor oldOperands wingBank).address (N:=nodeCap)
local notation "trueFront_" => matrixAt+17*DescentExteriorShelf.span j rest s E₀
local notation "placement_" => originalPlacement G rounds f g restart τ β n h C rot R src_
  trueFront_ lookupBase peerBank ((dateCalendar).homes sliceEnd) wingBank
local notation "channels_" => (pre).channels censusBase
local notation "placed_" => original_mask_and_replay_room G board rot rounds f g restart cut R dateDegree τ β payloadBits
  src_ branch headRate_ datesRate_ codeRate_ lastRate_ ratio₀ slots_ ordinary reset positive shorten fit
  siteCount dateDegree seedWire_ seedHist_ funding low dyadic le_rfl (Nat.le_pow_clog (by decide : 1<2) siteCount)
  le_rfl rfl placement_ channels_
private theorem purchasedCohortBeforeMask (spec : DescentTerminalPreflightSpace.Spec) (start bits : ℕ) (bound : spec.maskBase start < 2^bits) :
    spec.cohortEnd start < 2^bits := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉⟩ := spec.layers start
  exact (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans (h₇.trans (h₈.trans h₉)))))))).trans_lt bound

attribute [local irreducible] normalizedPackedChart SeedNamed.issued

open Lean Elab Term in
local elab "purchasedBound% " fn:term:arg "[" args:term,* "]" : term => do
  let e ← elabTerm fn none
  return mkAppN e (← args.getElems.mapM fun arg => elabTerm arg none)

local notation "paidPlacement" =>
  purchasedBound% (@originalPlacement) [F, (inferInstance : Field F), G, rounds, f, g, restart,
    τ, β, n, h, C, rot, R, payloadBits, src_, trueFront_, lookupBase, peerBank,
    ((dateCalendar).homes sliceEnd), wingBank]

set_option maxHeartbeats 12000000 in
include opened smaller low dyadic funding in
/-- The physical final date and its actual census fit in the purchased RAM word. -/
theorem purchased_census_replay_room : (dateCalendar).stop censusBase < 2^w := by
  have paid := purchasedBound% (@original_final_event_placement) [
    F, (inferInstance : Field F), G, n, h, board, rot, rounds, f, g, restart, cut, R, dateDegree, τ, β,
    payloadBits, src_, branch, headRate_, datesRate_, codeRate_, lastRate_, ratio₀, slots_,
    ordinary, reset, positive, shorten, fit, siteCount, dateDegree, seedWire_, seedHist_, funding,
    low, dyadic, (show siteCount ≤ siteCount from le_rfl), (Nat.le_pow_clog (by decide : 1<2) siteCount),
    (show dateDegree ≤ dateDegree from le_rfl), (Eq.refl R), paidPlacement, channels_]
  exact purchasedBound% (@purchasedCohortBeforeMask) [dateSpec, censusBase, w, paid.2.2.2.2.2.2.2.2.2]

local notation "replayRoom" => purchasedBound% (@purchased_census_replay_room)
    [F, (inferInstance : Field F), cp, P, X, G, n, h, C, f, g, rounds, restart, τ, β, siteCount, payloadBits,
      opened, smaller, low, dyadic, ordinary, reset, branch, positive, room, shorten, ratio₀, fit,
      headRate_, datesRate_, codeRate_, lastRate_, slots_, funding]

local notation "dateEntryAt" mu => (dateCalendar).memory sliceEnd censusBase replayRoom ((datePhase).memory earlyFloor (earlyImage mu))
local notation "primitiveOf" mu => (dateSpec).primitiveSnapshot (base:=censusBase) («w»:=w) («q»:=q) («p»:=p) (nd:=atomBits)
  (nodes:=nodeCap) (hidden:=cap) (args:=cap) (oldPaid:=paidBank) (actor:=actorBank) (first:=roleBanks) (second:=arityBanks)
  («chart»:=operandChart) (f0:=publicCell) (f7:=privateCell) ((lookupPage).image (dateEntryAt mu))
local notation "datedDecoder" => Branch.decodeBook S G base ordinary.radix p q 3
  (dateSpec).cap (dateSpec).printBits (by decide)
local notation "booksOf" mu => (dateSpec).bookSnapshot (base:=censusBase) («peer»:=peerBank) (wing:=wingBank)
  («w»:=w) («q»:=q) («p»:=p) (nd:=atomBits) (nodes:=nodeCap) (hidden:=cap) (args:=cap)
  (oldPaid:=paidBank) (actor:=actorBank) (first:=roleBanks) (second:=arityBanks) («chart»:=operandChart)
  (f0:=publicCell) (f7:=privateCell) (decode:=datedDecoder) ((lookupPage).image (dateEntryAt mu))
local notation "dateHomes" => (dateCalendar).homes sliceEnd

local notation "begin_" => censusBase
local notation "peer" => peerBank
local notation "old" => wingBank
local notation "org" => lookupBase
local notation "homes" => dateHomes
local notation "other" => AddressPlan.fixedFallback
local notation "arity" => max 8 (2^(S).capGain)
local notation "groups" => cap
local notation "stride" => R
local notation "oldTags" => DescentPrimitivePalette.colors G s Z rot
local notation "codec" => DescentPrimitivePalette.codec (G:=G) («s»:=s) («Z»:=Z) rot
local notation "tagCount" => DescentBundleTagKeys.capacity oldTags arity groups p stride
local notation "V" => (⟨q,tagCount,cap,nodeCap,cap,p,groupsAt⟩:Home.Format)
local notation "pages₀" => (pre).scanPages org q
local notation "total" => (pages₀).total
local notation "modulo" => (pages₀).modulo
local notation "boundary" => (pages₀).boundaries
local notation "T" => (RouteSources.Tables.mk 4 venues (venues*NativeBranch.localLimit G S)
  (NativeBranch.localLimit G S) (Book.tokenBits (venues*NativeBranch.localLimit G S)) W q K)
local notation "B" => (pre).pageBits
local notation "grain" => p
local notation "codes" => DescentTerminalScalarHeader.range q tagCount cap nodeCap cap p venues
local notation "seed" => (chart).seed
local notation "clockCap" => G.C
local notation "front" => end_ (lo+extent packWidth steps) clockCap packWidth+17*DescentExteriorShelf.span j rest s E₀
local notation "extra" => DescentTerminalPublicIdentity.total K W q piece codes rawWords count₀
local notation "Full" => DescentTerminalFullPins.Candidate ((chart).Pin⊕Hidden E₀ j rest s) K W q piece rawWords
local notation "power" => NativeBranch.copy_power S (radix:=ordinary.radix) base width
local notation "rom" => front+DescentTerminalChipBootWords.total K W q piece codes
local notation "I_" => (pre).reachedInput begin_ rom q piece W K codes front peer old total modulo homes
                          boundary cfg V other T (pre).vertices B
local notation "R_" => (pre).channels begin_
local notation "start" => (pre).maskBase begin_
local notation "base_" => afterMeter V cfg R_ start
local notation "A_" => rowArena cfg I_ base_
local notation "J_" => (pre).chipInput begin_ rom q grain peer old total modulo homes boundary cfg other

local notation "head" => startingHeader
local notation "short" => original_shell_short X G rounds depth_ f g restart siteCount τ payloadBits n h C rot R
local notation "literal" => ScalarLiterals.data q (V).roles (V).privateWords (V).nodes (V).addresses grain (pre).vertices W B
  (cfg).terminal.pool qh ((T).columns A_ (J_).sources) ((T).value (fun _ _=>0))
local notation "O_" => registers V cfg R_ start head
local notation "plan_" => AddressPlan.layout cfg I_ base_ O_

local notation "emptyCode" => (DescentTerminalChronologicalBooks.empty q tagCount cap nodeCap cap p venues p).val
local notation "bankSet" => DescentTerminalChipBootWords.chipBanks («K»:=K) («W»:=W) («q»:=q)
  («p»:=piece) codes (plan_).emit front emptyCode

local notation "wall" => AddressPlan.takeOff (cfg) I_ base_
local notation "compact" => end_ (lo+extent packWidth steps) G.C packWidth
local notation "firstFree" => front+extra
local notation "dst" => finalAt firstFree lo packWidth steps
local notation "seedBase" => DescentWideSeedFlags.endInput X (S).copies s payloadBits
local notation "seedRows" => DescentPackedSeed.rows X (S).copies s payloadBits
local notation "B₀" => (S).groupWidth k tail 0+k
open Chronology DescentDatedSeedStartup.Input DescentTerminalEpochDecoder DescentPackedSeed DescentExteriorShelf
local notation "capture" => seedBase+seedRows+1
local notation "fundedReel" => originalReplay G board rot rounds f g restart cut R τ β payloadBits src_
  branch ratio₀ ordinary reset positive shorten fit siteCount dateDegree seedWire_ seedHist_

include funding opened smaller low dyadic in
set_option maxHeartbeats 3000000 in
private theorem paidRoleReplayForPlacement (placing : TerminalPlacement)
    (channelSet : DescentTerminalVertexFields.MaskAllocation.Channels (S).radix) :
    (fundedReel).replayStart G rounds f g restart β src_ < 2^w :=
  original_replay_base_fits G board rot rounds f g restart cut R dateDegree τ β payloadBits src_ branch
    headRate_ datesRate_ codeRate_ lastRate_ ratio₀ slots_ ordinary reset positive shorten fit siteCount
    dateDegree seedWire_ seedHist_ funding low dyadic le_rfl (Nat.le_pow_clog (by decide : 1<2) siteCount)
    le_rfl rfl placing channelSet

include opened smaller in
set_option maxHeartbeats 3000000 in
private theorem boughtReplayNumber : (fundedReel).replayStart G rounds f g restart β src_ = replayBase := by
  unfold CensusReplay.replayStart CensusReplay.roleBase Hierarchy.DescentSixParty.SeedNamed.replayBase
  dsimp only [originalReplay]
  rfl

include funding opened smaller low dyadic in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem paidMeasuredReplay (placing : TerminalPlacement)
    (channelSet : DescentTerminalVertexFields.MaskAllocation.Channels (S).radix) : replayBase < 2^w :=
  (boughtReplayNumber X G rounds restart τ β siteCount payloadBits opened smaller ordinary reset branch positive
    room shorten ratio₀ fit).symm.trans_lt
    (paidRoleReplayForPlacement X G rounds restart τ β siteCount payloadBits opened smaller low dyadic
      ordinary reset branch positive shorten ratio₀ fit headRate_ datesRate_ codeRate_ lastRate_ slots_
      funding placing channelSet)

include funding opened smaller low dyadic in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
/-- The funded chart fits the replay start at the actual purchased role bank. -/
theorem purchased_role_replay_fits : replayBase < 2^w := by
  -- The funded upper bound is uniform in the bank origins. Its conclusion only
  -- references the replay start, so it suffices to evaluate it at address zero.
  let anchor : TerminalPlacement := originalPlacement G rounds f g restart τ β n h C rot R src_
    0 0 ⟨0,0⟩ ⟨0,0⟩ (fun _ _ => ⟨0,0⟩)
  let channels : DescentTerminalVertexFields.MaskAllocation.Channels (S).radix :=
    ⟨fun _ => ⟨0,0⟩, fun _ _ => ⟨0,0⟩⟩
  exact paidMeasuredReplay X G rounds restart τ β siteCount payloadBits opened smaller low dyadic
    ordinary reset branch positive room shorten ratio₀ fit headRate_ datesRate_ codeRate_ lastRate_ slots_
    funding anchor channels

local notation "replayFits" => purchased_role_replay_fits X G rounds restart τ β siteCount payloadBits
    opened smaller low dyadic ordinary reset branch positive room shorten ratio₀ fit headRate_ datesRate_
    codeRate_ lastRate_ slots_ funding

local notation "roleMount" => originalRoleMount G rot S p R roleBase replayBase le_rfl replayFits
local notation "captureDates" => countDates 0 (kindCalendar (S).rounds (S).height)
local notation "rowAddress" => fun i:ℕ=>countAt ((captureDates)[i]?.getD 0)
local notation "oldReel" => DescentExteriorMatrixUpdate.Calendar.reel S k tail replayBase dateTag dateRotation
local notation "matrixEnd" => DescentExteriorMatrixUpdate.Calendar.stop S k tail replayBase
local notation "termCode" => Branch.postEarlyPreflight X G S base ordinary.radix g p q R rot headerRows paidRows
  j rest s replayBase datePhase snapshots blockCast roleBase peerBank paidBank actorBank wingBank replayRoom
local notation "termCost" => Branch.postEarlyPreflightClocks X G S («k»:=k) («tail»:=tail) g p q R rot headerRows paidRows
  j rest s replayBase datePhase snapshots blockCast peerBank paidBank actorBank wingBank replayRoom
local notation "bootCode" => completeAfter G rot X ((S).initialDigits ordinary.radix) hostsEnough startup startingHeader payloadBits Z w
local notation "bootCost" => completeTicks («S»:=S) («k»:=k) G rot X hostsEnough startup payloadBits Z w
local notation "originalMid" => ((DateCode.afterBoot bootCode datesAt (S).length).seq
   (Branch.historyMountedReel X S replayBase dateTag dateRotation countAt capture matrixAt k tail j rest s w (roleMount).phase)).seq termCode
local notation "originalCost" => (DateCode.afterTicks bootCost datesAt (S).length+
    (((4+11*(captureDates).length)+(roleMount).phase.ticks)+DescentExteriorMatrixUpdate.Calendar.earlyClock S k tail j rest s datePorts))+termCost
local notation "upperFence" => (pre).maskBase censusBase
local notation "freshReel" => (oldReel).late upperFence
local notation "countSlot" => fun i:ℕ=>capture+i
local notation "fence" => upperFence
local notation "count" => countSlot
local notation "plan" => freshReel

local notation "middle" => originalMid
local notation "cost" => originalCost
local notation "initialFlag" => seedBase+seedRows
local notation "foldSites" => controlsAt firstFree lo G.C packWidth steps count (fun _=>initialFlag)
local notation "prefixCode" => DescentWideSeedFlags.check X (S).copies s payloadBits w
local notation "paidCode" => (((((prefixCode).seq ((middle).seq (relocate j rest s E₀ w compact wall))).seq
    ((plan).program j rest s E₀ w B₀ (S).length wall)).seq (fold w initialFlag dst foldSites)).seq
    (AddressPlan.clock V cfg I_ R_ start head short literal (bw:=w)))
local notation "paidTime" => ((4+(seedRows+1)*66+(cost+(4+18*(17*DescentExteriorShelf.span j rest s E₀))))+
    (10+((4+58*(S).length)+(4+16*E₀))))+bill initialFlag dst foldSites+AddressPlan.time V cfg I_ R_ start head
local notation "charge" => fun v=> (normalizedLeaf X G S ordinary reset branch positive room shorten v
  base width age wFit qFit qh cfg pool raw).debt cfg

local notation "extPins" => Port (((S).copies*s)*P) (copiesWidth ((S).copies*s) X.width)
local notation "view" x₀ => Branch.copyInput X s power x₀
local notation "bootFor" x₀:arg z₀:arg => Root.appended front extra
    (Root.widePackedImage X (S).copies s payloadBits w seed lo G.C packWidth steps compact
      (DescentExterior.publicRows X (view x₀)) (Sum.elim (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inl)
      (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inr)))
    (DescentTerminalPublicIdentity.back (z₀ ∘ DescentTerminalFullPins.chip) w codes count₀)

local notation "histAt" z₀ => (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inl)
local notation "checkedAt" x₀:arg z₀:arg => DescentWideSeedFlags.countedAt X (S).copies s payloadBits seed
  (histAt z₀) (bootFor x₀ z₀)
local notation "startedAt" x₀:arg z₀:arg => completeImage G rot X ((S).initialDigits ordinary.radix) hostsEnough startup
  startingHeader payloadBits Z (checkedAt x₀ z₀)
local notation "lastAt" x₀:arg z₀:arg => DateCode.history datesAt (startedAt x₀ z₀) (S).length
local notation "capturedAt" x₀:arg z₀:arg => (roleMount).phase.image (DescentLowCountBook.output capture rowAddress (lastAt x₀ z₀) (captureDates).length)
set_option maxHeartbeats 1800000 in
private def purchasedStageEntry : RegisterTimeline.Position := entry_

set_option maxHeartbeats 1800000 in
private def purchasedStageMenu := menu_

set_option maxHeartbeats 1800000 in
private def purchasedStageTraces := traces_

set_option maxHeartbeats 1800000 in
private def purchasedStageBootAt (x₀ : extPins → Bool) (z₀ : Full → Bool) : Computability.VPVNP.BurstRAM.Memory w := bootFor x₀ z₀

set_option maxHeartbeats 1800000 in
private def purchasedStageStartedMemory (rawMemory : Computability.VPVNP.BurstRAM.Memory w) : Computability.VPVNP.BurstRAM.Memory w :=
  completeImage G rot X ((S).initialDigits ordinary.radix) hostsEnough startup startingHeader payloadBits Z rawMemory

set_option maxHeartbeats 1800000 in
private def purchasedStageCountedMemory (z₀ : Full → Bool) (rawMemory : Computability.VPVNP.BurstRAM.Memory w) : Computability.VPVNP.BurstRAM.Memory w :=
  DescentWideSeedFlags.countedAt X (S).copies s payloadBits seed (histAt z₀) rawMemory


local notation "purchased_entry_" => (@purchasedStageEntry F _ cp P X G n h C f g rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten ratio₀ fit)
local notation "purchased_traces_" => (@purchasedStageTraces F _ cp P X G n h C f g rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten)
local notation "purchased_menu_" => (@purchasedStageMenu F _ cp P X G n h C f g rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten ratio₀ fit)
local notation "purchased_cursor_" => RegisterTimeline.calendar («w»:=w) purchased_traces_ purchased_menu_ purchased_entry_
local notation "purchased_datesAt" => RunTrace.machine purchased_traces_ (fun i _=>RegisterTimeline.instruction («w»:=w) purchased_traces_ purchased_menu_ purchased_entry_ i)
local notation "purchased_prior_" => purchased_cursor_ dateAge
local notation "purchased_ordinaryAt" => (purchased_menu_).ordinary
local notation "purchased_operandLanes" => (purchased_prior_).ports.operandLanes
local notation "purchased_primitiveLanes" => (purchased_prior_).ports.roleLanes
local notation "purchased_previousDate" => (purchased_prior_).ports.venue
local notation "purchased_priorAddress" => (purchased_prior_).ports.io.wire
local notation "purchased_rosterBank" => (purchased_prior_).ports.io.roster
local notation "purchased_datedFloor" => (purchased_prior_).ports.priorStart k (purchased_prior_).floor
local notation "purchased_dateRotation" => fun i=>(purchased_menu_).rotationAt G S k i (purchased_cursor_ i)
local notation "purchased_rankDir_" => RegisterTimeline.snapshotDirectory («w»:=w) purchased_traces_ purchased_menu_ purchased_entry_
local notation "purchased_snapshots" => SnapshotCalendar reset (kindCalendar (S).rounds (S).height)
  (capCalendar G.b (S).rounds g (S).height) purchased_rankDir_
local notation "purchased_rankFloor" => (purchased_cursor_ (S).length).floor
local notation "purchased_roleBase" => max purchased_rankFloor (matrixAt+32*DescentExteriorShelf.span j rest s E₀)
local notation "purchased_replayBase" => purchased_roleBase+DescentTerminalRoleTables.count (originalRoleBits G rot S p R)
local notation "purchased_dateMachine" => PhysicalReset.scheduled G S board k tail dateAge p f g R dateDegree datePayload purchased_ordinaryAt rot
  s Z purchased_operandLanes purchased_primitiveLanes purchased_previousDate purchased_priorAddress purchased_rosterBank purchased_datedFloor
local notation "purchased_bootFor" x₀:arg z₀:arg => (@purchasedStageBootAt F _ cp P X G n h C f g rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten base width ratio₀ fit x₀ z₀)
local notation "purchased_checkedAt" x₀:arg z₀:arg => (@purchasedStageCountedMemory F _ cp P X G n h C f g rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten ratio₀ fit z₀ (purchased_bootFor x₀ z₀))
local notation "purchased_startedAt" x₀:arg z₀:arg => (@purchasedStageStartedMemory F _ cp P X G n h C f g rounds restart τ β siteCount payloadBits opened smaller low dyadic ordinary reset branch positive room shorten ratio₀ fit headRate_ datesRate_ codeRate_ lastRate_ slots_ funding (purchased_checkedAt x₀ z₀))

set_option maxHeartbeats 4000000 in
private def purchasedRegisteredRowAt (c₀ : (last).Choice) (heldMemory : Computability.VPVNP.BurstRAM.Memory w) :=
  @WideRegisteredDateRows F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive
    room shorten c₀ j rest headerRows paidRows w h board dateAge dateDegree datePayload purchased_ordinaryAt purchased_operandLanes
    purchased_primitiveLanes purchased_previousDate purchased_priorAddress purchased_rosterBank purchased_datedFloor purchased_replayBase matrixAt purchased_dateRotation purchased_snapshots purchased_roleBase heldMemory

set_option maxHeartbeats 4200000 in
private def purchasedCapturedMemory (x₀ : extPins → Bool) (z₀ : Full → Bool) : Computability.VPVNP.BurstRAM.Memory w :=
  let countImage := purchasedEndCapture (width:=w) purchased_datesAt (purchased_startedAt x₀ z₀) (S).length capture
    (fun i => (purchased_menu_).selectorAt G S k i (purchased_cursor_ i)) (countDates 0 (kindCalendar (S).rounds (S).height))
  purchasedRoleLiteralImage G rot S p R purchased_roleBase countImage

set_option maxHeartbeats 3500000 in
/-- The scheduled register at the captured physical memory for the selected purchased-stage candidate. -/
def purchasedRegisteredFieldsAt (x₀ : extPins → Bool) (z₀ : Full → Bool) (c₀ : (last).Choice)
    (din : (purchased_dateMachine).DateInputs ((purchased_dateMachine).stageStart purchased_datedFloor) w) : Prop :=
  @purchasedRegisteredRowAt F _ cp P X G n h C f
    g rounds restart τ β siteCount payloadBits ordinary reset branch
    positive room shorten ratio₀ fit c₀ (@purchasedCapturedMemory F _ cp P X G n h C f g rounds restart τ β siteCount payloadBits opened smaller low dyadic ordinary reset branch positive room shorten base width ratio₀ fit headRate_ datesRate_ codeRate_ lastRate_ slots_ funding x₀ z₀) din

local notation "paidCapturedAt" x₀:arg z₀:arg =>
  @purchasedCapturedMemory F _ cp P X G n h C f g rounds restart τ β siteCount payloadBits opened smaller
    low dyadic ordinary reset branch positive room shorten base width ratio₀ fit headRate_ datesRate_
    codeRate_ lastRate_ slots_ funding x₀ z₀

open Lean Meta Elab Command Term Parser.Term in
local elab "purchasedProof " name:ident args:bracketedBinder* " := " proof:term : command => do
  let declName := mkPrivateName (← getEnv) ((← getCurrNamespace) ++ name.getId.eraseMacroScopes)
  let included := (← getScope).includedVars
  runTermElabM fun sectionVars => elabBinders (args.map (·.raw)) fun params => do
    let result ← elabTerm proof none
    synthesizeSyntheticMVarsNoPostponing
    let result ← mkLambdaFVars params (← instantiateMVars result)
    let mut needed := collectFVars (collectFVars {} result) (← inferType result)
    let mut captured := #[]
    for input in sectionVars.reverse do
      let decl ← input.fvarId!.getDecl
      if needed.fvarSet.contains decl.fvarId || included.contains decl.userName then
        needed := collectFVars needed decl.type
        captured := captured.push input
    let witness ← Term.levelMVarToParam (← mkLambdaFVars captured.reverse result)
    let statement ← inferType witness
    let levels := collectLevelParams (collectLevelParams {} statement) witness
    addDecl (.thmDecl {
      name := declName
      levelParams := levels.params.toList
      type := statement
      value := witness })

open Lean Meta Elab Term in
private meta def purchasedInputs (fn field : Syntax) (named : Array (TSyntax `ident)) :
    TermElabM Lean.Expr := do
  let declarationHead ← elabTerm fn none
  let inst ← elabTerm field none
  let explicitArgs ← named.mapM fun input => do
    return (input.getId.eraseMacroScopes, ← elabTerm input none)
  let lctx ← getLCtx
  let rec gather (type : Lean.Expr) (args : Array Lean.Expr) : TermElabM Lean.Expr := do
    match type with
    | .forallE name _ body info =>
      if info.isInstImplicit then gather body (args.push inst)
      else if let some suppliedInput := explicitArgs.find? (fun arg => arg.1 == name) then
        gather body (args.push suppliedInput.2)
      else
        let some decl := lctx.findFromUserName? name
          | throwError "missing purchased stage input {name}"
        gather body (args.push decl.toExpr)
    | .letE _ _ _ body _ => gather body args
    | _ => return mkAppN declarationHead args
  gather (← Lean.Meta.inferType declarationHead) #[]

local elab "scanInputs% " fn:term:arg "using" field:term:arg : term =>
  purchasedInputs fn field #[]

local elab "scanNamedInputs% " fn:term:arg "using" field:term:arg "with" "[" args:ident,* "]" : term =>
  purchasedInputs fn field args.getElems


private def purchasedScanPhase : DescentTerminalFixedSlices.Phase F := Phase.scheduled G S board k tail dateAge p f g R dateDegree datePayload purchased_ordinaryAt rot
  purchased_operandLanes purchased_primitiveLanes purchased_previousDate purchased_priorAddress purchased_rosterBank purchased_datedFloor
private def purchasedScanCalendar : DescentTerminalFixedReplay.Calendar k := replayCalendar X S k tail j rest purchased_snapshots
private def purchasedScanSpec : DescentTerminalPreflightSpace.Spec := dateSpec
private def purchasedScanEarlyFloor : ℕ := DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail purchased_replayBase j rest s datePorts
private def purchasedScanEarlyImage (captured : Memory w) : Memory w := DescentExteriorMatrixUpdate.Calendar.earlyImage S k tail purchased_replayBase dateTag purchased_dateRotation j rest s datePorts matrixAt captured

local notation "scanned_phase" => scanInputs% (@purchasedScanPhase) using (inferInstance : Field F)
local notation "scanned_calendar" => scanInputs% (@purchasedScanCalendar) using (inferInstance : Field F)
local notation "scanned_spec" => scanInputs% (@purchasedScanSpec) using (inferInstance : Field F)
local notation "scanned_floor" => scanInputs% (@purchasedScanEarlyFloor) using (inferInstance : Field F)
local notation "scanned_early_image" => scanInputs% (@purchasedScanEarlyImage) using (inferInstance : Field F)
local notation "scanned_slice" => (scanned_phase).stop scanned_floor

private def purchasedScanPage : DescentTerminalControlROMs.Page :=
  (scanned_spec).scanPages ((scanned_calendar).packetEnd scanned_slice) q
local notation "scanned_page" => scanInputs% (@purchasedScanPage) using (inferInstance : Field F)

private def purchasedScanResult {scanField : Type} [Field scanField] {divisions wordSize : ℕ}
    (phase₀ : DescentTerminalFixedSlices.Phase scanField) (cal₀ : DescentTerminalFixedReplay.Calendar divisions)
    (page₀ : DescentTerminalControlROMs.Page) (floor₀ slice₀ : ℕ) (bound₀ : cal₀.stop page₀.stop < 2^wordSize)
    (early₀ : Memory wordSize) : Memory wordSize :=
  page₀.image (cal₀.memory slice₀ page₀.stop bound₀ (phase₀.memory floor₀ early₀))

private def purchasedScannedImage (captured : Memory w)
    (bound : (scanned_calendar).stop (scanned_page).stop < 2^w) : Memory w :=
  purchasedBound% (@purchasedScanResult) [F, (inferInstance : Field F), k, w, scanned_phase, scanned_calendar,
    scanned_page, scanned_floor, scanned_slice, bound, scanned_early_image]


local notation "pp_dateHardware" => (scanned_phase).output.receiver
local notation "pp_dateBlocks" => (scanned_spec).scalar.blocks
local notation "pp_blockCast" => (rfl : pp_dateBlocks=(pp_dateHardware).blocks)
local notation "pp_paidBank" => fun x:Fin pp_dateBlocks=>(scanned_phase).output.terminalPaid (scanned_phase).dateBase x.val
local notation "pp_actorBank" => fun x:Fin pp_dateBlocks=>(scanned_phase).output.terminalActor (scanned_phase).dateBase x.val
local notation "pp_wingBank" => fun (x:Fin pp_dateBlocks) (a:Fin (2*(scanned_spec).cap))=>(scanned_phase).output.terminalWing (scanned_phase).dateBase x.val a.val
local notation "pp_roleBankBits" => fun roleField:Fin 6=>DescentTerminalCombinedRole.width dateColors (max 8 (2^(S).capGain))
  cap p R roleField*((S).epochPower^(S).localTokenExponent)*(scanned_spec).groups
local notation "pp_publicCell" => DescentTerminalPointerDigits.publicCell («cap»:=(scanned_spec).cap) (N:=nodeCap) (A:=cap)
  (d:=(scanned_spec).scalar.pointerBits) 3 q G.b (poolBatchCount (s*1) p) (k*(S).length) (scanned_spec).groups operandWidths
local notation "pp_privateCell" => DescentTerminalPointerDigits.output (scanned_spec).cap nodeCap cap 3 (scanned_spec).groups
  (scanned_spec).scalar.pointerBits (Nat.clog 2 (q+cap+1)) q G.b (poolBatchCount (s*1) p) operandWidths terminalPin
local notation "pp_roleBanks" => DescentTerminalRoleTables.role pp_roleBankBits ((scanned_phase).banks scanned_floor) roleBase
local notation "pp_arityBanks" => DescentTerminalRoleTables.arity pp_roleBankBits ((scanned_phase).banks scanned_floor) roleBase
local notation "pp_pointerBank" => fun (pointerField:Fin 4) (slot:Fin (scanned_phase).output.argumentSlots) (block:Fin pp_dateBlocks) =>
  (scanned_phase).output.terminalPointers (scanned_phase).dateBase pointerField slot (block.cast pp_blockCast)
local notation "pp_oldOperands" => DescentTerminalOperandRepack.padded («K»:=cap) pp_pointerBank pp_paidBank
local notation "pp_operandChart" => ((scanned_spec).pointerPages (scanned_page).stop matrixFloor pp_oldOperands pp_wingBank).address (N:=nodeCap)

private def purchasedPrimitiveFromScan (sourceImage : Memory w) : Memory w :=
  purchasedBound% (@DescentTerminalPreflightSpace.Spec.primitiveSnapshot)
    [scanned_spec, (scanned_page).stop, w, q, p, atomBits, nodeCap, cap, cap,
     pp_paidBank, pp_actorBank, pp_roleBanks, pp_arityBanks, pp_operandChart,
     Nat.clog 2 (q+1)*(scanned_spec).groups, (Nat.clog 2 (q+cap+1)*(nodeCap*cap))*(scanned_spec).groups,
     pp_publicCell, pp_privateCell, sourceImage]


private def purchasedPacketPrimitive (captured : Memory w)
    (bound : (scanned_calendar).stop (scanned_page).stop < 2^w) : Memory w :=
  let sourceImage : Memory w := scanInputs% (@purchasedScannedImage) using (inferInstance : Field F)
  scanNamedInputs% (@purchasedPrimitiveFromScan) using (inferInstance : Field F) with [sourceImage]

local notation "bphase_" => scanInputs% (@purchasedScanPhase) using (inferInstance : Field F)
local notation "bcal_" => scanInputs% (@purchasedScanCalendar) using (inferInstance : Field F)
local notation "bpage_" => scanInputs% (@purchasedScanPage) using (inferInstance : Field F)
local notation "bfloor_" => scanInputs% (@purchasedScanEarlyFloor) using (inferInstance : Field F)
private def acquiredBookRoleBase : ℕ := roleBase
private def acquiredBookMatrixFloor : ℕ := matrixFloor
local notation "brole_" => scanInputs% (@acquiredBookRoleBase) using (inferInstance : Field F)
local notation "bmatrix_" => scanInputs% (@acquiredBookMatrixFloor) using (inferInstance : Field F)
private def purchasedBookFromScanned (sourceImage : Memory w) : Memory w :=
  purchasedBound% (@acquiredGeometryBooks) [F, (inferInstance : Field F), cp, P, X, G, S, k, g, p, tail, q, R,
    rot, headerRows, paidRows, base, ordinary.radix, bphase_, (@Eq.refl ℕ (2^k)),
    bfloor_, brole_, bmatrix_, (bpage_).stop, w, sourceImage]
private def purchasedPacketBooks (captured : Memory w) (bound : (bcal_).stop (bpage_).stop < 2^w) : Memory w :=
  let sourceImage : Memory w := scanInputs% (@purchasedScannedImage) using (inferInstance : Field F)
  scanNamedInputs% (@purchasedBookFromScanned) using (inferInstance : Field F) with [sourceImage]


set_option maxHeartbeats 8000000 in
private def purchasedPacketRows (c₀ : (last).Choice) (primitiveMem booksMem : Memory w) : Prop :=
  purchasedBound% (@WideMeasuredPackets)
    [F, (inferInstance : Field F), cp, P, X, G, S, k, cut, tail, n, h, C, f, g, W, q, piece,
      ordinary, reset, branch, positive, room, shorten, c₀, j, rest, base, width, headerRows, paidRows, w,
      censusBase, peerBank, wingBank, lookupBase, ((dateCalendar).homes sliceEnd), primitiveMem, booksMem]


private def purchasedPaidPacketsAt (x₀ : extPins → Bool) (z₀ : Full → Bool) (c₀ : (last).Choice) : Prop :=
  let captured : Memory w := scanInputs% (@purchasedCapturedMemory) using (inferInstance : Field F)
  let bound := scanInputs% (@purchased_census_replay_room) using (inferInstance : Field F)
  let primitiveMem : Memory w := scanNamedInputs% (@purchasedPacketPrimitive) using (inferInstance : Field F) with [captured, bound]
  let booksMem : Memory w := scanNamedInputs% (@purchasedPacketBooks) using (inferInstance : Field F) with [captured, bound]
  scanNamedInputs% (@purchasedPacketRows) using (inferInstance : Field F) with [primitiveMem, booksMem]

local notation "primitiveBank" => fun (x₀:extPins→Bool)(z₀:Full→Bool)=>primitiveOf (capturedAt x₀ z₀)
local notation "booksBank" => fun (x₀:extPins→Bool)(z₀:Full→Bool)=>booksOf (capturedAt x₀ z₀)
local notation "selectedAt" z₀ => (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow (histAt z₀)
local notation "honestAt" z₀ => issued X G S ordinary reset branch positive room shorten (selectedAt z₀)
local notation "acceptAt" z₀ => ∃c,(chart).read (histAt z₀)=some c
local notation "layout_" => fun c=>Branch.publicLayout X G S (issued X G S ordinary reset branch positive room shorten c)
  positive base width
local notation "whichAt" x₀:arg z₀:arg => proposed (chart).read layout_ (DescentExterior.publicRows X (view x₀))
  (z₀ ∘ DescentTerminalFullPins.history)
variable (scalarRoom : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
  (fun epoch pitch frozen =>
    let split := NativeBranch.binLimit («k»:=pitch) epoch
    let localChunk := headChunk G epoch
    let socketCount := 2^localChunk*(G.b^(epoch.rounds*epoch.height)*G.b)
    let grainSize := headGrain G epoch pitch payloadBits
    let seedWidth := epoch.firstWidth G.b grainSize
    let rotor := RotorSpec.ofRates reset
    let historySize := max 1 (max reset.bitsR (C*reset.bitsR))
    let privateSlots := NativeBranch.privateSlotCapacity G epoch historySize
    let colors := DescentPrimitivePalette.colors G seedWidth (epoch.grainAt G.b grainSize 0) rotor
    let tags := DescentBundleTagKeys.capacity colors (max 8 (2^epoch.capGain)) privateSlots grainSize historySize
    let rowCount := terminalPool X G epoch grainSize socketCount split n h C f g
    let format := Branch.geometryFormat G epoch pitch g grainSize frozen socketCount historySize rotor rowCount rowCount
    let preflight := Branch.preflightSpec X G epoch pitch g grainSize frozen
      ({format with binSize:=split} : Branch.PreflightFormat)
    EarnedScalarArguments localChunk seedWidth grainSize socketCount split tags
      preflight.pageBits preflight.printBits payloadBits (ratio₀*payloadBits)))
local notation "machine" => (show sliceWidth W q piece ≤ w from
  purchasedMachineWidth scalarRoom.packed (heads_).embed)

local notation "cols" => AddressPlan.observationColumns V cfg I_ R_ start head dst

local notation "candidatePrior" => wideChoicePrior X G S ordinary reset branch positive room shorten w fit base width
local notation "seedNet" => wideChoiceCircuit («K»:=K) («W»:=W) («q»:=q) («piece»:=piece) X G S ordinary reset branch positive room shorten w fit («j»:=j) («rest»:=rest) cfg
local notation "numBins" => DescentTerminalChronologicalBooks.Keys q tagCount cap nodeCap cap p venues p
local notation "numSlots" => (cfg).terminal.pool
local notation "cpu" => AddressPlan.chip cfg I_ base_
local notation "tapeDesc" => (cols).tape cpu (K*W)
local notation "widthWord" => q*p

local notation "countWidth_" => w+1
local notation "readoutEnd_" => AddressPlan.last V cfg I_ R_ start
local notation "cut_" => DescentTerminalLast.trailingCut readoutEnd_ (cfg).terminal.rows
local notation "stop_" => DescentTerminalLast.trailingStop cut_ rawWords numSlots numBins
local notation "terminalWord_" => original_replay_word G board rot rounds f g restart cut R dateDegree τ β payloadBits
  src_ branch headRate_ datesRate_ codeRate_ lastRate_ ratio₀ slots_ ordinary reset positive shorten fit
  siteCount dateDegree seedWire_ seedHist_ funding low dyadic le_rfl (Nat.le_pow_clog (by decide : 1<2) siteCount)
  le_rfl rfl placement_ R_

private theorem purchased_slice_stop_eq {K₀ : Type} [Field K₀] {G₀ : PoweredGadget K₀} {A : AtomSchedule}
    {bits delay height : ℕ} {P₀ : DescentTerminalFixedSlices.Phase K₀} (fields₀ : FinalSliceFields G₀ A bits delay height P₀) (start₀ : ℕ) :
    P₀.stop start₀ = AddressPlan.sliceStop start₀ P₀.output.argumentSlots P₀.digits (2^bits) (A.hostSize A.length) :=
  congrArg₂ (AddressPlan.sliceStop start₀ P₀.output.argumentSlots P₀.digits) fields₀.blocks fields₀.hosts

set_option maxHeartbeats 5000000 in
include opened smaller low dyadic funding in
private theorem purchased_stage_scan_agrees :
    censusBase = censusScanBase G rounds f g restart τ β n h C rot R src_ fundedReel := by
  have numeric := purchasedBound% (@original_final_event_geometry) [
    F, (inferInstance : Field F), G, n, h, board, rot, rounds, f, g, restart, cut, R, dateDegree, τ, β,
    payloadBits, src_, branch, headRate_, datesRate_, codeRate_, lastRate_, ratio₀, slots_,
    ordinary, reset, positive, shorten, fit, siteCount, dateDegree, seedWire_, seedHist_, funding,
    low, dyadic, (show siteCount ≤ siteCount from le_rfl), (Nat.le_pow_clog (by decide : 1<2) siteCount),
    (show dateDegree ≤ dateDegree from le_rfl)]
  have splice := purchasedBound% (@purchased_slice_stop_eq)
    [F, (inferInstance : Field F), G, S, k, R, payloadBits, datePhase, numeric.1, earlyFloor]
  let queued := fun e : ℕ => ((dateSpec).scanPages ((dateCalendar).packetEnd e) q).stop
  exact congrArg queued splice

set_option maxHeartbeats 12000000 in
include opened smaller low dyadic funding in
purchasedProof purchased_physical_terminal_word :=
  paidWordAtPhysicalScan%
    (purchasedBound% (@grid_original_terminal_word_fit) [
      F, (inferInstance : Field F), G, n, h, board, rot, rounds, f, g, restart, cut, R, dateDegree, τ, β,
      payloadBits, src_, branch, headRate_, datesRate_, codeRate_, lastRate_, ratio₀, slots_,
      ordinary, reset, positive, shorten, fit, siteCount, dateDegree, seedWire_, seedHist_, funding,
      low, dyadic, (show siteCount ≤ siteCount from le_rfl), (Nat.le_pow_clog (by decide : 1<2) siteCount),
      (show dateDegree ≤ dateDegree from le_rfl), (Eq.refl R), paidPlacement, channels_])
    (purchasedBound% (@purchased_stage_scan_agrees)
      [F, (inferInstance : Field F), cp, P, X, G, n, h, C, f, g, rounds, restart, τ, β, siteCount, payloadBits,
        opened, smaller, low, dyadic, ordinary, reset, branch, positive, room, shorten, ratio₀, fit,
        headRate_, datesRate_, codeRate_, lastRate_, slots_, funding])

local notation "censusRoom" => purchasedBound% (@purchased_physical_terminal_word)
    [F, (inferInstance : Field F), cp, P, X, G, n, h, C, f, g, rounds, restart, τ, β, siteCount, payloadBits,
      opened, smaller, low, dyadic, ordinary, reset, branch, positive, room, shorten, ratio₀, fit,
      headRate_, datesRate_, codeRate_, lastRate_, slots_, funding]

local notation "banks_" => DescentTerminalLast.trailingBanks w numSlots numBins cut_ rawWords
  (Nat.lt_trans (Nat.lt_succ_self _) censusRoom)
local notation "fed" => (paidCode).seq (DescentTerminalChipRuntime.program cpu bankSet w (K*W) numSlots)
local notation "whole" => DescentTerminalReadout.complete tapeDesc banks_ («cut»:=cut_) (stop:=stop_) (rows:=rawWords) (word:=widthWord) fed
local notation "pcs" => (whole).labels+3
local notation "regs" => (whole).registers+1
local notation "binsPaid" => Fintype.card Unit+numBins+1
local notation "obs" => rawWords+binsPaid
local notation "fuel" => paidTime+clocks (K*W) numSlots+ticks tapeDesc banks_ rawWords widthWord+3
local notation "runtime" => CheapISA.hostFuel fuel

local notation "sitePagesAt" x₀:arg z₀:arg c₀:arg => WideEarnedSitePages (X:=X) (G:=G) («S»:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh)
      («template»:=template) (sitesPositive:=sitesPositive) («rawWords»:=rawWords) («headerRows»:=headerRows)
      («paidRows»:=paidRows) («pool»:=pool) («raw»:=raw) (payloadBits:=payloadBits) (fit:=fit) («rom»:=rom)
      («other»:=other) («lo»:=lo) («packWidth»:=packWidth) («head»:=head)
      («fence»:=fence) («count»:=count) («plan»:=plan) («codec»:=codec) («short»:=short) (all:=z₀) (c:=c₀)
      (original:=view x₀) («board»:=board) («dateAge»:=dateAge) («dateDegree»:=dateDegree)
      («datePayload»:=datePayload) («ordinaryAt»:=ordinaryAt) («operandLanes»:=operandLanes) («primitiveLanes»:=primitiveLanes)
      («previousDate»:=previousDate) («priorAddress»:=priorAddress) («rosterBank»:=rosterBank)
      («datedFloor»:=datedFloor) («replayBase»:=replayBase) (matrixTable:=matrixAt) («dateTag»:=dateTag)
      («dateRotation»:=dateRotation) («snapshots»:=snapshots) («roleBase»:=roleBase) («replayRoom»:=replayRoom)
      (datedMem:=capturedAt x₀ z₀)


set_option maxHeartbeats 7500000 in
/-- The issued branch matrix as a word read from the purchased replay directory. -/
private def purchasedMatrixRead (c₀ : (last).Choice) (mu : Memory w) : Prop :=
  mu matrixFloor =
  ((DescentExterior.matrixCode (Branch.pinSpine X G S (issued X G S ordinary reset branch positive room shorten c₀)
    positive base).matrix).val:Computability.VPVNP.BurstRAM.Word w)
local notation "matrixAtSource" x₀:arg z₀:arg c₀:arg => primitiveBank x₀ z₀ matrixFloor =
  ((DescentExterior.matrixCode (Branch.pinSpine X G S (issued X G S ordinary reset branch positive room shorten c₀)
    positive base).matrix).val:Computability.VPVNP.BurstRAM.Word w)
local notation "paidPacketsAt" x₀:arg z₀:arg c₀:arg => WideMeasuredPackets (X:=X) (G:=G) («S»:=S) (ordinary:=ordinary)
  (reset:=reset) (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (c:=c₀)
  (base:=base) (width:=width) («headerRows»:=headerRows) («paidRows»:=paidRows)
  («begin_»:=censusBase) («peer»:=peerBank) («old»:=wingBank) («org»:=lookupBase) («homes»:=dateHomes)
  (primitive:=primitiveBank x₀ z₀) (m:=booksBank x₀ z₀)
local notation "registeredAt" x₀:arg z₀:arg c₀:arg din:arg => WideRegisteredDateRows
    («q»:=q) («j»:=j) («rest»:=rest) («W»:=W) («piece»:=piece) (X:=X) (G:=G) («S»:=S) (ordinary:=ordinary)
    (reset:=reset) (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (c:=c₀)
    («board»:=board) («dateAge»:=dateAge) («dateDegree»:=dateDegree) («datePayload»:=datePayload)
    («ordinaryAt»:=ordinaryAt) («operandLanes»:=operandLanes) («primitiveLanes»:=primitiveLanes)
    («previousDate»:=previousDate) («priorAddress»:=priorAddress) («rosterBank»:=rosterBank)
    («datedFloor»:=datedFloor) («replayBase»:=replayBase) (matrixTable:=matrixAt) («dateRotation»:=dateRotation)
    («snapshots»:=snapshots) («roleBase»:=roleBase) (dateInput:=din) (datedMem:=capturedAt x₀ z₀)
    («headerRows»:=headerRows) («paidRows»:=paidRows)

local notation "sourceWordsAt" x₀:arg z₀:arg c₀:arg => OriginalSiteWords (X:=X) (G:=G) («S»:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (c:=c₀) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh) («template»:=template) (sitesPositive:=sitesPositive) («rawWords»:=rawWords) («headerRows»:=headerRows) («paidRows»:=paidRows) («pool»:=pool) («raw»:=raw) («board»:=board) («dateAge»:=dateAge) («dateDegree»:=dateDegree) («datePayload»:=datePayload) («ordinaryAt»:=ordinaryAt) («operandLanes»:=operandLanes) («primitiveLanes»:=primitiveLanes) («previousDate»:=previousDate) («priorAddress»:=priorAddress) («rosterBank»:=rosterBank) («datedFloor»:=datedFloor) («replayBase»:=replayBase) (matrixTable:=matrixAt) («dateTag»:=dateTag) («dateRotation»:=dateRotation) («snapshots»:=snapshots) («roleBase»:=roleBase) (datedMem:=capturedAt x₀ z₀)  («replayRoom»:=replayRoom)

local notation "invoice_" price:arg =>
  (4*((seedNet).cells+(seedNet).internal)+9*(rawWords*widthWord)+binsPaid*countWidth_+
    Fintype.card Full+Fintype.card extPins+
    (257*(1000*(2*(7*(ratio₀+6))+2)*(2*4^7+1))+256*fixedISAPrice*(ratio₀+6))*
      (pcs+regs+firstFree+fuel+obs+2^payloadBits+1)*(payloadBits+1))*2^depth_≤
        price*((S).copies*s)*(siteCount+2^depth_*E₀)

open Lean Meta Elab Term in
local elab "purchasedStageInputs% " fn:term:arg "using" field:term:arg : term => do
  let declarationHead ← elabTerm fn none
  let inst ← elabTerm field none
  let lctx ← getLCtx
  let rec gather (type : Lean.Expr) (args : Array Lean.Expr) : TermElabM Lean.Expr := do
    match type with
    | .forallE name _ body info =>
      if info.isInstImplicit then gather body (args.push inst)
      else
        let some decl := lctx.findFromUserName? name
          | throwError "missing purchased stage input {name}"
        gather body (args.push decl.toExpr)
    | .letE _ _ _ body _ => gather body args
    | _ => return mkAppN declarationHead args
  gather (← Lean.Meta.inferType declarationHead) #[]

attribute [local irreducible] WideMeasuredPackets
open Lean Elab Term in
/-- Compare the matrix word in the same primitive memory used in the measured row. -/
local elab "matrixFromPurchasedPackets " packetPred:term:arg matrixPred:term:arg : term => do
  let measured ← elabTerm packetPred none
  let revealed ← Meta.whnf measured
  unless revealed.getAppFn.isConstOf ``WideMeasuredPackets do
    throwError "expected the acquired physical packet fields"
  let physicalInput := revealed.getAppArgs[revealed.getAppNumArgs-2]!
  let matrixPredicate ← elabTerm matrixPred none
  return mkApp matrixPredicate physicalInput

private def purchasedPhysicalMatrixAt (x₀:extPins→Bool) (z₀:Full→Bool) (c₀:(last).Choice) : Prop :=
  matrixFromPurchasedPackets
    (purchasedStageInputs% (@purchasedPaidPacketsAt) using (inferInstance : Field F))
    (purchasedBound% (@purchasedMatrixRead) [F, (inferInstance : Field F), cp, P, X, G, n, h, C, f, g, rounds, restart,
      τ, β, siteCount, payloadBits, ordinary, reset, branch, positive, room, shorten, base, ratio₀, fit, c₀])

def purchasedCandidateMatches (x₀ : extPins → Bool) (z₀ : Full → Bool) (c₀ : (last).Choice) : Prop :=
  candidatePrior x₀ (erased z₀) = some c₀

/-- The original-site word predicate at the registered date, after capture and role mounting. -/
private abbrev purchasedOriginalSiteReceipt (x₀:extPins→Bool) (z₀:Full→Bool) (c₀:(last).Choice) : Prop :=
  purchasedBound% (@OriginalSiteWords) [F, (inferInstance : Field F), cp, P, X, G, S, k, cut, tail, n, h, C, f, g,
    W, q, piece, ordinary, reset, branch, positive, room, shorten, c₀, j, rest, base, width, age,
    wFit, qFit, qh, template, sitesPositive, rawWords, headerRows, paidRows, pool, raw, w, h, board,
    dateAge, dateDegree, datePayload, ordinaryAt, operandLanes, primitiveLanes, previousDate,
    priorAddress, rosterBank, datedFloor, replayBase, matrixAt, dateTag, (show ℕ → ℕ from dateRotation),
    snapshots, roleBase, (show Memory w from paidCapturedAt x₀ z₀), replayRoom]


private def purchasedStageObservation {ExteriorDomain SecondDomain CandidateDomain DateDomain : Type}
    (selected : ExteriorDomain → SecondDomain → CandidateDomain → Prop)
    (registered : ExteriorDomain → SecondDomain → CandidateDomain → DateDomain → Prop)
    (packets matrix sourceWords : ExteriorDomain → SecondDomain → CandidateDomain → Prop) : Prop :=
  ∀ (x : ExteriorDomain) (z : SecondDomain) (c : CandidateDomain),
    selected x z c → ∀ din : DateDomain, registered x z c din →
      packets x z c → matrix x z c → sourceWords x z c

open Lean Meta Elab Term in
/-- Use the four physical input types already checked by the registered row. -/
local elab "purchasedPhysicalObservation% "
    selected:term:arg registered:term:arg packets:term:arg matrix:term:arg words:term:arg
    " using " fieldInst:term:arg : term => do
  let ctx ← getLCtx
  let fieldTerm ← elabTerm fieldInst none
  let stageHead (syntaxTerm : Syntax) := do
    let predicateHead ← elabTerm syntaxTerm none
    let rec applyStage (ty : Lean.Expr) (args : Array Lean.Expr) : TermElabM Lean.Expr := do
      match ty with
      | .forallE nm _ body bi =>
        if nm == `x₀ then return mkAppN predicateHead args
        if bi.isInstImplicit then applyStage body (args.push fieldTerm)
        else
          let some localDecl := ctx.findFromUserName? nm
            | throwError "missing parameter {nm} in purchased stage field {predicateHead}"
          applyStage body (args.push localDecl.toExpr)
      | _ => throwError "expected an exterior input binder in the purchased stage field {predicateHead}"
    applyStage (← inferType predicateHead) #[]
  let fieldPreds ← #[selected, registered, packets, matrix, words].mapM (fun stx => stageHead stx)
  let registeredTy ← inferType fieldPreds[1]!
  let rec readTypes (ty : Lean.Expr) (acc : Array Lean.Expr) : TermElabM (Array Lean.Expr) := do
    if acc.size == 4 then return acc
    let .forallE _ dom body _ := ty | throwError "expected the four original registered row arguments"
    if dom.hasLooseBVars then throwError "the registered row uses a dependent input domain"
    readTypes body (acc.push dom)
  let types ← readTypes registeredTy #[]
  return mkAppN (mkConst ``purchasedStageObservation) (types ++ fieldPreds)

private abbrev purchasedStageObserved : Prop :=
  purchasedPhysicalObservation% (@purchasedCandidateMatches) (@purchasedRegisteredFieldsAt)
    (@purchasedPaidPacketsAt) (@purchasedPhysicalMatrixAt) (@purchasedOriginalSiteReceipt) using (inferInstance : Field F)

/-- The three primitive fields on each selected original RAM row, after the paid late replay. -/
structure PurchasedStageReceipts : Prop where
  observed : purchasedStageInputs% (@purchasedStageObserved) using (inferInstance : Field F)

local notation "tariff_" => originalHostPrice G rounds f g restart n h C ratio₀ τ

open Lean Meta Elab Term in
private def purchasedFinalEventTemplate (argCount : Nat) : TermElabM Lean.Expr := do
  let census ← getConstInfo ``purchased_census_replay_room
  let some proof := census.value? (allowOpaque := true)
    | throwError "missing proof of the purchased census bound"
  lambdaTelescope proof fun inputs result => do
    let some placementApp := result.find? (·.isAppOfArity ``original_final_event_placement 43)
      | throwError "the census proof has no 43-argument final event placement"
    if placementApp.hasLooseBVars then
      throwError "the census placement depends on an inner binder"
    let event ← if argCount == 43 then pure placementApp else if argCount == 40 then
      pure (mkAppN (mkConst ``original_final_event_geometry) (placementApp.getAppArgs.extract 0 40))
    else throwError "expected either 43 event placement inputs or 40 event geometry inputs"
    mkLambdaFVars inputs event (etaReduce := false)

open Lean Meta Elab Term in
local elab "purchasedEventFromCensus% " argCount:num " using " censusProof:term:arg : term => do
  let application := (← elabTerm censusProof none).consumeMData
  unless application.isAppOfArity ``purchased_census_replay_room 35 do
    throwError "expected the actual 35-argument purchased census bound"
  let eventProofFunction ← purchasedFinalEventTemplate argCount.getNat
  return eventProofFunction.beta application.getAppArgs



open Lean Meta Elab Term in
local elab "purchasedReplayArea% " placement:term:arg : term => do
  let input := (← elabTerm placement none).consumeMData
  let event ← if input.isFVar then do
      let decl ← input.fvarId!.getDecl
      let some definition := decl.value? | throwError "expected the local final event placement definition"
      pure definition.consumeMData
    else pure input
  unless event.isAppOfArity ``original_final_event_placement 43 do
    throwError "expected the actual 43-argument event placement application"
  return mkProj ``And 0 (mkAppN (mkConst ``original_replay_word) event.getAppArgs)

open Lean Meta Elab Term in
local elab "purchasedPort105% " localName:ident " using " callback:term:arg : term => do
  let context ← getLCtx
  let some purchasedPrefixDecl := context.findFromUserName? localName.getId <|> context.findFromUserName? localName.getId.eraseMacroScopes
    | throwError "missing the checked purchased prefix local {localName.getId}"
  let some stored := purchasedPrefixDecl.value?
    | throwError "the purchased prefix local has no defining application"
  let application := (← instantiateMVars stored).consumeMData
  let parameters := application.getAppArgs
  let donor := application.getAppFn
  unless donor.isConst do throwError "expected a constant-headed call in the purchased prefix"
  let mut residual := (← inferType donor).consumeMData
  for _ in [:parameters.size] do
    match residual with
    | .forallE _ _ body _ => residual := body.consumeMData
    | _ => throwError "the funded host or checked prefix parameter spine ended early"
  residual := (residual.instantiateRev parameters).consumeMData
  for _ in [:256] do
    match residual with
    | .letE _ _ val body _ => residual := (body.instantiate1 val).consumeMData
    | _ => break
  if !residual.isForall then
    residual := (← whnf residual).consumeMData
  let .forallE portName domain _ _ := residual
    | throwError "could not expose earned in {donor} after {parameters.size} inputs, residual head {residual.getAppFn.constName?.getD .anonymous}, metavariable {residual.isMVar}, application {residual.isApp}, let {residual.isLet}"
  unless portName == `earned do
    throwError "the genuine residual should begin with earned, found {portName}"
  withoutErrToSorry <| elabTerm callback (some domain)

open Lean Meta in
private def purchasedStageAfterPrefix (root : Lean.Expr) (inputs : Array Lean.Expr) : MetaM Lean.Expr := do
  unless inputs.size == 104 do throwError "the original funded host prefix requires 104 inputs"
  let mut stageTelescope ← inferType root
  for _ in [:inputs.size] do
    let .forallE _ _ remainder _ := stageTelescope.consumeMData
      | throwError "the funded host type ends before the prefix"
    stageTelescope := remainder
  let .forallE purchasedCallbackBinder _ _ _ := stageTelescope.consumeMData | throwError "the funded host has no callback"
  unless purchasedCallbackBinder == `earned do throwError "the prefix should end before earned, found {purchasedCallbackBinder}"
  return stageTelescope.instantiateRev inputs

open Lean Meta Elab Term in
local elab "purchasedTypedPrefix104% " "<|" term:term : term => do
  let value := (← withoutErrToSorry <| elabTerm term none).consumeMData
  let residual ← purchasedStageAfterPrefix value.getAppFn value.getAppArgs
  return mkExpectedPropHint value residual

open Lean Meta Elab Term in
local elab "purchasedCheckedPrefix% " fn:term:arg " using " field:term:arg : term => do
  let prefixHead ← elabTerm fn none
  let fieldInst ← elabTerm field none
  let context ← getLCtx
  let mut spine := (← inferType prefixHead).consumeMData
  let mut args := #[]
  for _ in [:256] do
    match spine with
    | .forallE nm _ body bi =>
      let value ← if bi.isInstImplicit then pure fieldInst else do
        let some localDecl := context.findFromUserName? nm
          | throwError "missing parameter {nm} for the checked purchased host prefix"
        pure localDecl.toExpr
      args := args.push value
      if nm == `dates then return mkAppN prefixHead args
      spine := body.consumeMData
    | .letE _ _ purchasedLetValue body _ =>
      spine := (body.instantiate1 purchasedLetValue).consumeMData
    | _ => throwError "reached the end of the purchased host prefix before its dates argument"
  throwError "unexpected binder count for the purchased host prefix"

-- The first 104 purchased host inputs have their own kernel-checked declaration.
-- The returned proof still expects the original 20 later inputs.
set_option maxHeartbeats 40000000 in
include scalarRoom in
purchasedProof purchasedFundedThrough104 (words:HostWordRoom G S k tail p j ratio₀ payloadBits)
    (dates:StageDateResources G rot rounds f g restart R dateDegree n h τ β payloadBits siteCount w)
    :=
  let headPaid := purchasedBound% (@original_head_placement) [
    F, (inferInstance : Field F), G, n, h, board, rot, rounds, f, g, restart,
    cut, R, τ, β, payloadBits, src_, branch, ratio₀, ordinary, reset, positive,
    shorten, fit, siteCount, dateDegree, seedWire_, seedHist_, K, (Nat.le_succ K)]

  let actualPlacement := purchasedEventFromCensus% 43 using (replayRoom)
  let shops := conjunctionPort% actualPlacement 0 10
  let live := conjunctionPort% actualPlacement 1 10
  let metadata := conjunctionPort% actualPlacement 2 10
  let one := conjunctionPort% actualPlacement 3 10
  let roleEnd := conjunctionPort% actualPlacement 4 10
  let layout := conjunctionPort% actualPlacement 5 10
  let paid := conjunctionPort% actualPlacement 6 10
  let signed := conjunctionPort% actualPlacement 7 10
  let scanAgreement := purchasedBound% (@purchased_stage_scan_agrees) [
      F, (inferInstance : Field F), cp, P, X, G, n, h, C, f, g, rounds, restart, τ, β, siteCount, payloadBits,
      opened, smaller, low, dyadic, ordinary, reset, branch, positive, room, shorten, ratio₀, fit,
      headRate_, datesRate_, codeRate_, lastRate_, slots_, funding]
  let headBelowPhysical : startingHeader < censusBase :=
    physicalHeadRoom% (headPaid.headerBelow) using scanAgreement
  purchasedTypedPrefix104% <| purchasedBound% (@original_funded_stage_host) [
    F, (inferInstance : Field F), cp, P, X, G,
    cut, n, h, C, f, g,
    rounds, restart, τ, β, siteCount, payloadBits,
    ordinary, reset, branch, positive, room, shorten,
    base, width, age, wFit, qFit, qh,
    template, sitesPositive, pool, raw, w, fit,
    bootHosts, hostsEnough, startup, startingHeader, dateDegree, replayRoom,
    other, short, replayFits, machine, censusRoom, (R+1),
    ratio₀, words.seedWord, words.epochWord, words.edgeWord, words.seatsWord, headPaid.reelAbove,
    headBelowPhysical, (show head < front+extra ∨ dst < head from Or.inr headPaid.afterVotes), shops, live, metadata, one,
    roleEnd, layout, paid, signed, words.retainedWidth, words.replayPayload,
    (heads_).signed, (heads_).fields, (heads_).low, (heads_).source, (heads_).live, (heads_).embed,
    (heads_).boot, datesRate_, headRate_, dateDegree, (heads_).grant, (heads_).old,
    (heads_).returned, (heads_).receiver, (heads_).growth, smaller, (heads_).input, (show dateDegree ≤ dateDegree from le_rfl),
    (heads_).first, (heads_).geometry, (heads_).groups, (heads_).headerFits, (heads_).machine, dates.matcher,
    dates.signed, dates.palette, (Nat.two_pow_pos j), (heads_).observations, (heads_).degree, dates.degree,
    dates.snapshot, (heads_).paid, words.batchFit, headPaid.archiveEnd, headPaid.reelData, headPaid.below,
    headPaid.headLow, (show head < capture ∨ capture+(captureDates).length ≤ head from Or.inr headPaid.captureBefore)]

set_option maxHeartbeats 90000000 in
include scalarRoom in
/-- The single native input and its fixed paid price suffice at this height. The same public
calendar and last register are used for every tagged ballot. -/
theorem purchased_stage_instance (words:HostWordRoom G S k tail p j ratio₀ payloadBits)
    (dates:StageDateResources G rot rounds f g restart R dateDegree n h τ β payloadBits siteCount w)
    (purchased:OriginalPurchaseAt G rot rounds f g restart n h C R dateDegree ratio₀ τ β payloadBits)
    (receipts:PurchasedStageReceipts (X:=X) (G:=G) (opened:=opened) (smaller:=smaller)
      (low:=low) (dyadic:=dyadic) (ordinary:=ordinary) (reset:=reset) (branch:=branch)
      (positive:=positive) (room:=room) (shorten:=shorten) (base:=base) (width:=width) (age:=age)
      (wFit:=wFit) (qFit:=qFit) (qh:=qh) (sitesPositive:=sitesPositive) (fit:=fit)
      (funding:=funding))
    (isa:ISAFromInvoice G rounds f g restart τ β ratio₀ tariff_ payloadBits siteCount X) :
    ∃calls:ℕ,∃H:Host F cp (((S).copies*s)*P)
        (Sockets (List.replicate calls (CollapseOracle.tagCall payloadBits (referenceReplacement (F:=F) payloadBits cp)))),
      Agrees (independentCopies ((S).copies*s) X) (tableApprox H.width (exactValue _ H)) ∧
      hostSize H*2^depth_≤tariff_*((S).copies*s)*(siteCount+2^depth_*E₀) :=by
  let headPaid := purchasedBound% (@original_head_placement) [
    F, (inferInstance : Field F), G, n, h, board, rot, rounds, f, g, restart,
    cut, R, τ, β, payloadBits, src_, branch, ratio₀, ordinary, reset, positive,
    shorten, fit, siteCount, dateDegree, seedWire_, seedHist_, K, (Nat.le_succ K)]

  let actualPlacement := purchasedEventFromCensus% 43 using (replayRoom)
  let live := conjunctionPort% actualPlacement 1 10
  let metadata := conjunctionPort% actualPlacement 2 10
  let signedPitch := conjunctionPort% actualPlacement 8 10
  let mask := conjunctionPort% actualPlacement 9 10
  let actualShell := shape_
  let headerRoom := conjunctionPort% actualShell 2 10
  let hdrPos := conjunctionPort% actualShell 3 10
  let chipRows := conjunctionPort% actualShell 4 10
  let fixedPool := conjunctionPort% actualShell 5 10
  let leaves := conjunctionPort% actualShell 6 10
  let slots := conjunctionPort% actualShell 7 10
  let numeric := purchasedEventFromCensus% 40 using (replayRoom)
  let heightMatch := purchasedDyadicHeight dyadic
  have narrow : payloadBits+1≤w := purchasedInputRoom words.height words.wide
  have scanAgreement := purchasedBound% (@purchased_stage_scan_agrees) [
      F, (inferInstance : Field F), cp, P, X, G, n, h, C, f, g, rounds, restart, τ, β, siteCount, payloadBits,
      opened, smaller, low, dyadic, ordinary, reset, branch, positive, room, shorten, ratio₀, fit,
      headRate_, datesRate_, codeRate_, lastRate_, slots_, funding]
  have romBeforePhysical : rom + DescentTerminalDenseHeaderBoot.extent q p ≤ (pre).literalBase censusBase :=
    physicalLiteralRoom% (headPaid.romTop) using scanAgreement
  have invoice :=
    purchasedBound% (@grid_original_bought_price) [F, (inferInstance : Field F), cp, P, X, G, cut, n, h, C, f, g, rounds, restart, τ, β,
      siteCount, payloadBits, ordinary, reset, branch, positive, room, shorten, base, qh, template, sitesPositive, w,
      fit, bootHosts, hostsEnough, startup, startingHeader, dateDegree, replayRoom, other, short, replayFits, censusRoom,
      ratio₀, dateDegree, codeRate_, seedWire_, seedHist_, purchased, funding.calendar.invoice,
      Eq.refl w, narrow, (lt_of_lt_of_le (by decide : 0 < 4) words.height), low, smaller, dyadic,
      heightMatch, Nat.le_refl dateDegree, Eq.refl startup, Eq.refl startingHeader, Eq.refl template, Eq.refl other,
      (conjunctionPort% numeric 0 4), (conjunctionPort% numeric 3 4), metadata]
  let actualFundedPrefix := purchasedCheckedPrefix% (@purchasedFundedThrough104) using (inferInstance : Field F)
  let earned := purchasedPort105% actualFundedPrefix using
    (fun x₀ z₀ c₀ ok din date packets matrixRead dense => by
      have area := originalPaidAreaAtCensus% (purchasedReplayArea% actualPlacement) (funding.finalFits) (words.height) scanAgreement
      exact purchasedEarnedOnPage% [din, payloadBits, date, packets,
        (Eq.refl _), scalarRoom, chipRows, chipRows, fixedPool, leaves, headerRoom,
        original_rom_end K W q piece codes rawWords count₀ front,
        headPaid.reelData, headPaid.afterVotes.trans headPaid.headLow,
        (Nat.le_refl _), area, dense, receipts.observed x₀ z₀ c₀ ok din date packets matrixRead])
  let actualISA := actualPaidBounds% isa, invoice, ratio₀
  let hp := conjunctionPort% actualISA 0 4
  let hr := conjunctionPort% actualISA 1 4
  let ht := conjunctionPort% actualISA 2 4
  let ha := conjunctionPort% actualISA 3 4
  have packedWidth : q*p≤w := purchasedPackedWidth scalarRoom.packed (heads_).embed
  exact purchasedBound% actualFundedPrefix [earned, signedPitch, mask, live,
    romBeforePhysical, headerRoom, hdrPos, chipRows, packedWidth, words.word,
    slots, hp, hr, ht, ratio₀, words.height,
    (show w ≤ ratio₀*payloadBits from le_rfl), ha, tariff_, invoice]


end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
