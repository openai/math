import OAI.Hierarchy.BudgetSelectedOccupiedPorts
import OAI.Hierarchy.TaggedWideSelectedSignedEntry
import OAI.Hierarchy.TaggedWideSelectedSignedWidths
import OAI.Hierarchy.TaggedWideSelectedSignedLow
import OAI.Hierarchy.TaggedWideSelectedSignedBounds
import OAI.Hierarchy.TaggedWideSignedControlRoom

namespace OAI
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.Tagged.PassiveWindow
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe WireTelescope NamedAperture

private theorem selectedCarriedQuantities {siteCount fieldCount capBound : ℕ} {Seat : Type}
    (endpoints : Fin fieldCount → Chord siteCount) (siteId : Fin siteCount)
    (seatAt : (qty : Fin fieldCount → ℕ) → EndsAt endpoints qty siteId ↪ Seat)
    {qty0 qty1 : Fin fieldCount → ℕ} (eqQty : qty0 = qty1)
    (fits0 : ∀i, qty0 i ≤ capBound) (fits1 : ∀i, qty1 i ≤ capBound) {totalWidth : Widths siteCount}
    (shape0 : installedWidths endpoints qty0 = totalWidth) (shape1 : installedWidths endpoints qty1 = totalWidth) :
    carried endpoints qty0 siteId fits0 (seatAt qty0) shape0 =
      carried endpoints qty1 siteId fits1 (seatAt qty1) shape1 := by
  subst qty1
  rfl

end Hierarchy.Tagged.PassiveWindow

namespace Hierarchy.ProtocolRAM.SiteControls
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ProbeStage ProbeStage.CoreBoard ProbeStage.ReportSockets ProbeStage.CoreBoard.HistoryRoles WireTelescope NamedAperture Tagged PassiveWindow
open ThreeFlat.RAM DescriptorExpr
open AdaptiveProbe Computability.VPVNP.BurstRAM PrivateRAM DatedRoleSheets
open scoped Classical Fin.CommRing BigOperators
variable {h W k attempts N native n left right depth rom : ℕ} {S : PurchaseSampler}
  {π : Equiv.Perm (Fin (2^h))} {mark : Marks h W k attempts} {unique : Exclusive mark}
  {rows : Fin N≃Source S π depth mark} {pre mid id : Fin N→ℕ} {m : Memory native}
local notation "sites" => siteLast h (2^W) k+1
local notation "D" => stride k S.degree attempts
local notation "bits" => ProtocolRAMPurchaseSampler.bits (sites*D)
local notation "ends" => sorted S π depth mark ∘ rows
local notation "port" => named S π depth mark unique rows
local notation "raw" block => columns («D»:=D) n block sites bits (RoleROM.bank rom sites) .row
local notation "seat" qty:arg s:arg => PacketNeighbor.localSlot ends qty port (shelfSlot (h:=h) (W:=W) (k:=k) (attempts:=attempts) S)
  (named_coordinate S π depth mark unique rows) s
variable (oldSheet : ∀f,roleFact n S π depth mark unique rows left pre id m f)
    (newSheet : ∀f,roleFact n S π depth mark unique rows right mid id m f)
    (strides : RoleROM.Mounted rom (fun i : Fin (siteLast h (2^W) k+1)=>i.val*stride k S.degree attempts) m)
    (s : Fin (siteLast h (2^W) k+1)) (cap : ℕ) (rest want offer : Widths (siteLast h (2^W) k+1))
    (preBound : ∀i,pre i≤cap) (midBound : ∀i,mid i≤cap)
    (preShape : installedWidths (sorted S π depth mark ∘ rows) pre=rest+want) (midShape : installedWidths (sorted S π depth mark ∘ rows) mid=rest+offer)
local notation "l" => carried ends pre s preBound (seat pre s) preShape
local notation "r" => carried ends mid s midBound (seat mid s) midShape
local notation "col" => fun b : Bool=>raw (if b then right else left)
local notation "atPort" g => fun p : (portGraph sites).Port s => (g : Widths sites) p.val.1
local notation "reg" => (s.val:Word native)

private theorem castChosenWord {P : Type} {width : ℕ} (slotOwner : Option P) (quantity : P → ℕ) :
    slotOwner.elim (0 : Word width) (fun p => (quantity p : Word width)) = (↑(slotOwner.elim 0 quantity) : Word width) := by
  cases slotOwner <;> rfl

include oldSheet newSheet strides in
private theorem selected_two_ballot_fields
    (shelf fieldCount firstLow : ℕ)
    (sized : firstLow+(D+D)≤fieldCount)
    (ballotRoom : sites*fieldCount≤2^native)
    (slotIndex : Bool→Fin D→Fin fieldCount)
    (indexAt : ∀side slotId,(slotIndex side slotId).val=firstLow+side.toNat*D+slotId.val)
    (storedOld : ∀slotId, m (shelf+1+s.val*fieldCount+(slotIndex false slotId).val)=
        ((l).owner slotId).elim (0 : Word native) (fun p => ((want p.val.1 : ℕ) : Word native)))
    (storedNew : ∀slotId, m (shelf+1+s.val*fieldCount+(slotIndex true slotId).val)=
        ((r).owner slotId).elim (0 : Word native) (fun p => ((offer p.val.1 : ℕ) : Word native)))
    (one : 1<2^native) (siteRoom : sites≤2^native) (spanRoom : sites*D≤2^native)
    (sortedIds : StrictMono id) (idFit : ∀i,id i<2^native) (doubleFit : 2*cap<2^native)
    (beforeRoom : ∀p : (portGraph sites).Port s,(rest+want) p.val.1≤cap)
    (middleRoom : ∀p : (portGraph sites).Port s,(rest+offer) p.val.1≤cap) :
    CompiledFields m reg (atPort rest) (atPort want) (atPort offer) l r col
      (lowFieldFrom firstLow sites (shelf+1) fieldCount) := by
  have capSmall : cap<2^native := by omega
  have lowBefore := fun slotId => signed_low_from_word shelf fieldCount firstLow false slotId s m sized ballotRoom
    ((l).owner slotId) (atPort want) (fun p => (Nat.le_add_left ..).trans_lt ((beforeRoom p).trans_lt capSmall))
    (slotIndex false slotId) (indexAt false slotId) ((storedOld slotId).trans (castChosenWord _ _))
  have lowAfter := fun slotId => signed_low_from_word shelf fieldCount firstLow true slotId s m sized ballotRoom
    ((r).owner slotId) (atPort offer) (fun p => (Nat.le_add_left ..).trans_lt ((middleRoom p).trans_lt capSmall))
    (slotIndex true slotId) (indexAt true slotId) ((storedNew slotId).trans (castChosenWord _ _))
  exact signed_measured_pair oldSheet newSheet strides s cap rest want offer preBound midBound preShape midShape
    _ lowBefore lowAfter one siteRoom spanRoom sortedIds idFit doubleFit beforeRoom middleRoom


private theorem selectedCarriedOwnerPositive {numSites numRows qtyCap digits : ℕ}
    (endsAtRow : Fin numRows → Chord numSites) (amounts : Fin numRows → ℕ) (chosenSite : Fin numSites)
    (bounded : ∀ idx, amounts idx ≤ qtyCap) (placed : EndsAt endsAtRow amounts chosenSite ↪ Fin digits)
    {total : Widths numSites} (measuredShape : installedWidths endsAtRow amounts = total) :
    ∀ q party, (carried endsAtRow amounts chosenSite bounded placed measuredShape).owner q = some party →
      0 < (carried endsAtRow amounts chosenSite bounded placed measuredShape).width q := by
  intro q party occupies
  exact (seat_owned endsAtRow amounts chosenSite bounded placed measuredShape q).1 (by simp only [occupies, Option.isSome_some])

end Hierarchy.ProtocolRAM.SiteControls
end

/-! # The actual signed control words and both incoming role lookups at an elected site -/
noncomputable section

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open TaggedPrune CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option cleanup.letToHave false
set_option maxRecDepth 12288
set_option maxHeartbeats 1800000
universe uRoleCode
private theorem readPaidRoleFamily {Tape : Sort uRoleCode} (family : Tape → Prop) {funded recorded : Tape}
    (same : funded=recorded) (read : family recorded) : family funded := by
  cases same
  exact read

open CoreBoard.HistoryRoles in
open Lean Meta Elab Term in
private def datedRoleFieldAtFundedCode (sheet equalCode : Lean.Expr) (correctedBoundary : Option Lean.Expr) : MetaM Lean.Expr := do
  let eqType := (← inferType equalCode).consumeMData
  unless eqType.isAppOfArity ``Eq 3 do throwError "expected the actual selected code equality"
  let operands := eqType.getAppArgs
  forallBoundedTelescope (← inferType sheet) (some 1) fun fields _ => do
    unless fields.size == 1 do throwError "expected one physical role field"
    let original := mkAppN sheet fields
    let predicate := (← inferType original).consumeMData
    unless predicate.isAppOfArity ``DatedRoleSheets.roleFact 18 do
      throwError "expected a literal dated role field"
    let args := predicate.getAppArgs
    let protectedInput ← match correctedBoundary with
      | none => pure none
      | some boundary => do
        let some amount := args[14]!.find? fun candidate =>
          candidate.isAppOf ``wideCorrectedWidths && candidate.appArg! == boundary
          | throwError "missing corrected quantity at the actual successor boundary"
        let pieces := amount.getAppArgs
        unless pieces.size ≥ 3 do throwError "incomplete corrected quantity"
        let held := pieces[pieces.size-3]!
        if held.hasLooseBVars then throwError "spill-input witness contains a loose binder"
        pure (some held)
    withLocalDeclD `actualCode operands[0]! fun aliasName => do
      let mut updated := args
      for i in [0:args.size] do
        if i != 13 && i != 16 then
          let newArg := args[i]!.replace fun part =>
            if protectedInput.any (· == part) then some part
            else if part == operands[2]! then some aliasName else none
          updated := updated.set! i newArg
      let body := (mkAppN predicate.getAppFn updated).abstract #[aliasName]
      unless body.hasLooseBVars do throwError "no literal path code on this role field"
      let family := Lean.mkLambda `selectedCode BinderInfo.default operands[0]! body
      let level ← getLevel operands[0]!
      let proof := mkAppN (mkConst ``readPaidRoleFamily [level])
        #[operands[0]!,family,operands[1]!,operands[2]!,equalCode,original]
      mkLambdaFVars fields proof


open Lean Meta Elab Term in
local elab "selectedPaidSheet% " payment:term ", " codes:term ", " index:ident ", " processor:ident ", " mode:ident : term => do
  let actual := fun (syntaxTerm : Syntax) => do
    let body ← withSynthesize (postpone := .no) <| elabTerm syntaxTerm none
    let body ← instantiateMVars body
    if body.hasMVar then throwErrorAt syntaxTerm "unresolved physical input"
    pure body
  let paid ← actual payment
  let same ← actual codes
  let t ← getFVarFromUserName index.getId
  let left := fun (v : Lean.Expr) => Lean.Expr.proj ``And 0 v
  let right := fun (v : Lean.Expr) => Lean.Expr.proj ``And 1 v
  let processing ← match processor.getId.eraseMacroScopes with
    | `processing => pure (left paid)
    | `control => pure (right paid)
    | _ => throwErrorAt processor "expected processing or control"
  match mode.getId.eraseMacroScopes with
  | `past => do
    let prior ← mkAppM ``Fin.castSucc #[t]
    datedRoleFieldAtFundedCode (mkApp (left (right processing)) prior) (left same) none
  | `corrected => do
    let later ← mkAppM ``Fin.succ #[t]
    let zero ← elabTerm (← `((0 : Fin 3))) none
    datedRoleFieldAtFundedCode (mkAppN (right (right processing)) #[zero,later]) (left same) (some later)
  | _ => throwErrorAt mode "expected past or corrected"


variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
    {N : ℕ} (x : WideParent κ A) (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x)
    (rate : v.sharpPaidUnit≤unitCost) (support : v.SelectedReturnSupport m ell short u δ ξ unitCost rate x)
local notation "h" => x.h
local notation "width" => x.w
local notation "d" => 2^v.W
local notation "g" => v.wideDated h width ell unitCost
local notation "S" => v.wideInstalledSize x m ell unitCost g
local notation "Sfit" => (v.wide_installed_tape_bounds x m ell unitCost g).2.2
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unitCost g
    (v.wide_dated_sites h width ell unitCost) (v.wide_dated_edges h width ell unitCost) (fun _=>0)
local notation "reader" => v.wideSelector h width cpu.age cpu.ready.credit cpu.ready.size_le
local notation "sl" => (reader).format.slot
local notation "es" => events v.mesh
local notation "menu" => (typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ
local notation "slots" => purchaseSlots h v.W k v.wideJobs ell
variable (prices : v.PhysicalCounts u A δ ξ m) {C : ℝ} (pricePos : 0≤κ)
    (buy : ∀t:Fin (m+1),Purchased F menu x t slots
      (purchaseCandidates h v.W k v.wideJobs slots ((menu).height t x) (purchaseModules v.W u δ ξ menu x t))
      (purchaseModules v.W u δ ξ menu x t) C)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unitCost≤2^ell)
variable {b : Fin k→ℕ} (e : OpenPins h width b→Bool) (perm : Equiv.Perm (Tagged.Row h))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun i=>e (.inl i)))
local notation "base" => v.wideOrigin h width S seed perm
variable (j : Path sl es base)
local notation "report" => v.wide_reported_path h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le
    Sfit support.size.late support.size.words j
local notation "bought" => v.wide_selected_local_return m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j

local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unitCost g
local notation "first" => (lay).pruneScratch+(lay).pruneRows+1
local notation "rootROM" => v.wideInstalledRoot x
local notation "top" => (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh
local notation "rankEnd" => v.wideSpillRankEnd h width v.maxBits first
variable (t : Fin (events v.mesh).length) (a : Attempt) (onDate : (events v.mesh).get t=.attempt a)

local notation "extent" => (v.wide_funded_extent h width v.maxBits).trans Sfit
local notation "chosen" => CalendarTape.Prefix.pathVisitAt j t onDate
local notation "date" => v.wide_funded_date_with h width S extent perm seed cpu.age cpu.ready.credit
  cpu.ready.size_le (chosen).prior (chosen).choice (chosen).future
local notation "reference" => v.wide_reference_date h width S extent perm seed cpu.age cpu.ready.credit
  cpu.ready.size_le (chosen).prior
local notation "window" => (reader).format.windows
local notation "record" => CalendarTape.encode sl es base j
local notation "chart" => v.wideSignedChart h width (v.fixedTerminalStock (v.widePlacement h width) h width)
local notation "memo" => v.wide_selected_ballot_snapshots m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j false t a onDate


open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open WideControlJoin WireTelescope.PassMatrix WideCPU
local notation "G₀" => (v.wideFullGates x m ell short u δ ξ unitCost cpu.room).2
local notation "W₀" => Native.wordBits h d Native.copies
local notation "P₀" => v.widePlacement h width
local notation "S₀" => siteLast h d k+1
local notation "R₀" => (reference).2
local notation "age₀" => support.size.tenderAge
local notation "floor₀" => support.size.widthFloor
local notation "sector" => v.wideSpillDates h width ell unitCost v.maxBits first
local notation "sw" => (sector).roleRoot rankEnd 2
local notation "returned" => (bought).2.2.2.choose
local notation "dmd" => fun l=>((R₀).row extent age₀ floor₀ l).input
local notation "rewired" => fun l=>((R₀).tender extent age₀ floor₀ l).post ((chosen).choice l)
local notation "degree" => v.widePacketDegree
local notation "cap" => v.wideNeighborCap width unitCost
local notation "sh" => v.widePacketShape h width (.attempt a)

open HistoryRoles NamedAperture Tagged.PassiveWindow SiteControls WideCPU
local notation "W" => Native.wordBits h d Native.copies
local notation "preStart" => (g).roleStart S t.castSucc
local notation "postStart" => (sector).dateRole rankEnd t 0
local notation "rank" => (support.size.spill cpu.room)
local notation "entered" => v.wide_selected_packet_reads m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j false t a onDate
local notation "images" => v.wide_selected_role_images m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j false t a onDate
variable (height : v.BranchRoleHeight h width) (routeAge : v.routingHeight≤h)
local notation "leftWidth" => v.selected_signed_input_width m ell short u δ ξ unitCost x cpu perm j height t a onDate routeAge
local notation "rightWidth" => v.selected_signed_offer_width m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j height t a onDate routeAge
local notation "nativeRows" => v.selectedSignedRowBounds m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j height t a onDate
local notation "inputParts" => v.selectedSignedInputParts m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j height t a onDate
local notation "offerParts" => v.selectedSignedOfferParts m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j height t a onDate
local notation "pack" => v.wide_selected_signed_low m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j false t a onDate
local notation "key" => v.selectedPreclipCode m ell short u δ ξ unitCost x cpu perm j t a onDate
local notation "word" => v.PartyWordBounds h width unitCost
local notation "issued" => (R₀).occupiedBallots extent age₀ floor₀
local notation "heads" => v.widePacketLowStart h width (.attempt a)
local notation "count" => (v.widePacketShape h width (.attempt a)).columns

private def passiveOf {K : ℕ} {active passive added : Widths K} (_ : active=passive+added) := passive

/- Close adjacent dependent bindings together so each large selected proposition
is abstracted once across their shared local context. -/
open Lean Elab Term in
private partial def elaborateSelectedFieldBindings (body : Syntax) (locals : Array Lean.Expr) : TermElabM Lean.Expr := do
  let finish := fun () => do
    let value ← withSynthesize (postpone := .no) <| elabTerm body none
    let value ← instantiateMVars value
    if value.hasExprMVar then throwErrorAt body "unresolved physical argument in the selected signed field"
    Meta.mkLetFVars locals value (usedLetOnly := false) (generalizeNondepLet := false)
  unless body.isOfKind ``Lean.Parser.Term.«let» || body.isOfKind ``Lean.Parser.Term.«have» do
    return ← finish ()
  let i := if body[1].isOfKind ``Lean.Parser.Term.letConfig then 2 else 1
  let declaration := body[i][0]
  unless declaration.isOfKind ``Lean.Parser.Term.letIdDecl do return ← finish ()
  let view := mkLetIdDeclView declaration
  unless view.binders.isEmpty do return ← finish ()
  let expected ← if declaration[2].getNumArgs == 0 then pure none else some <$> elabType view.type
  let value ← withRef view.value <| withSynthesize (postpone := .no) <| elabTerm view.value expected
  let value ← instantiateMVars value
  let type ← match expected with | some type => pure type | none => Meta.inferType value
  let type ← instantiateMVars type
  if value.hasExprMVar || type.hasExprMVar then
    throwErrorAt view.value "unresolved argument in selected field {view.id}"
  Meta.withLetDecl view.id.getId type value fun localValue =>
    elaborateSelectedFieldBindings body[i+2] (locals.push localValue)

open Lean Elab Term in
local elab "selectPhysicalFields% " body:term : term => elaborateSelectedFieldBindings body #[]


private theorem atPhysicalDay {Day : Type} (family : Day → Prop) {funded physical : Day}
    (dayEquation : funded = physical) (measured : family funded) : family physical := by
  cases dayEquation
  exact measured

open Lean Meta Elab Term in
local elab "atPhysicalDay% " measurement:term ", " dayEquation:term : term => do
  let actual := fun (stx : Syntax) => do
    let raw ← withSynthesize (postpone := .no) <| elabTerm stx none
    let raw ← instantiateMVars raw
    if raw.hasExprMVar then throwErrorAt stx "unresolved physical date measurement"
    pure raw
  let measured ← actual measurement
  let eqProof ← actual dayEquation
  let typeEq := (← inferType eqProof).consumeMData
  let some (dayType,paidStageExpr,visitedStageExpr) := typeEq.eq? | throwErrorAt dayEquation "expected selected funded index equality"
  let predicate := (← inferType measured).consumeMData
  withLocalDeclD `modelDate dayType fun index => do
    let expanded := predicate.replace fun part => if part == paidStageExpr then some index else none
    let body := expanded.abstract #[index]
    unless body.hasLooseBVars do throwErrorAt measurement "the original date is absent from this measurement"
    let family := Lean.mkLambda `modelDate BinderInfo.default dayType body
    return mkAppN (mkConst ``atPhysicalDay) #[dayType,family,paidStageExpr,visitedStageExpr,eqProof,measured]

open CoreBoard.HistoryRoles in
open Lean Meta Elab Term in
local elab "measuredControlAtPaidSite% " data:term,+ : term => do
  let syntaxArgs := data.getElems
  unless syntaxArgs.size == 29 do throwError "expected the two control sheets, purchased table words and the native bounds"
  let xs ← syntaxArgs.mapM fun stx => do
    let value ← withSynthesize (postpone := .no) <| elabTerm stx none
    let value ← instantiateMVars value
    if value.hasExprMVar then throwErrorAt stx "unresolved signed-port input"
    pure value
  let roles := fun (sheet : Lean.Expr) => do
    let z ← elabTerm (← `((0 : Fin 3))) none
    let result := (← inferType (mkApp sheet z)).consumeMData.headBeta.consumeMData
    unless result.isAppOfArity ``DatedRoleSheets.roleFact 18 do throwError "expected actual mounted role fields"
    pure result.getAppArgs
  let old ← roles xs[0]!
  let corrected ← roles xs[1]!
  let mounted := (← inferType xs[2]!).consumeMData
  unless mounted.isAppOf ``RoleROM.Mounted do throwError "expected the actual mounted stride ROM"
  let bankArgs := mounted.getAppArgs
  let romBase := bankArgs[bankArgs.size-3]!
  let args : List (Name × Lean.Expr) := [
    (`h,old[1]!),(`W,old[2]!),(`k,old[3]!),(`attempts,old[4]!),(`N,old[5]!),(`native,old[6]!),
    (`n,old[0]!),(`left,old[13]!),(`right,corrected[13]!),(`depth,old[9]!),(`rom,romBase),
    (`S,old[7]!),(`π,old[8]!),(`mark,old[10]!),(`unique,old[11]!),(`rows,old[12]!),
    (`pre,old[14]!),(`mid,corrected[14]!),(`id,old[15]!),(`m,old[16]!),
    (`oldSheet,xs[0]!),(`newSheet,xs[1]!),(`strides,xs[2]!),(`s,xs[3]!),(`cap,xs[4]!),
    (`rest,xs[5]!),(`want,xs[6]!),(`offer,xs[7]!),(`preBound,xs[8]!),(`midBound,xs[9]!),
    (`preShape,xs[10]!),(`midShape,xs[11]!),
    (`shelf,xs[12]!),(`fieldCount,xs[13]!),(`firstLow,xs[14]!),(`sized,xs[15]!),(`ballotRoom,xs[16]!),
    (`slotIndex,xs[17]!),(`indexAt,xs[18]!),(`storedOld,xs[19]!),(`storedNew,xs[20]!),
    (`one,xs[21]!),(`siteRoom,xs[22]!),(`spanRoom,xs[23]!),(`sortedIds,xs[24]!),(`idFit,xs[25]!),
    (`doubleFit,xs[26]!),(`beforeRoom,xs[27]!),(`middleRoom,xs[28]!)]
  let info ← getConstInfo ``selected_two_ballot_fields
  let fn := Lean.mkConst info.name (info.levelParams.map fun _ => Level.zero)
  forallTelescope (← inferType fn) fun binders _ => do
    let actualArgs ← binders.mapM fun arg => do
      let keyName := (← arg.fvarId!.getDecl).userName.eraseMacroScopes
      let some storedOperand := args.lookup keyName | throwError "unrecognized measured control field {keyName}"
      pure storedOperand
    return mkAppN fn actualArgs

private theorem selectedShapeRoom {original printed : WideCPU.Shape} {numSites limit : ℕ}
    (sameShape : original = printed) (paid : numSites * original.columns < limit) :
    numSites * printed.columns ≤ limit := by
  cases sameShape
  exact paid.le

private theorem selectedDoubleColumns {firstColumnNumber halfColumnCount finalColumnCount : ℕ}
    (both : firstColumnNumber + 2 * halfColumnCount ≤ finalColumnCount) : firstColumnNumber + (halfColumnCount + halfColumnCount) ≤ finalColumnCount := by
  simpa only [two_mul] using both

private theorem selectedQuantityAtDate {Date Value : Type} (quantityAt : Date → Value)
    {purchasedDate printedDate : Date} (sameDate : purchasedDate = printedDate) :
    quantityAt printedDate = quantityAt purchasedDate := congrArg quantityAt sameDate.symm

private theorem selectedFactAtEqualValue {Value : Type} (pred : Value → Prop) {before after : Value}
    (eqVal : before = after) (physicalFact : pred before) : pred after := by
  cases eqVal
  exact physicalFact

open Lean Meta Elab Term in
private def rawPartsInReads (raw : Lean.Expr) : MetaM Lean.Expr := do
  forallTelescope (← inferType raw) fun _ native => do
    let some view ← whnfUntil native ``PacketTurns.NeighborReads | throwError "expected actual neighbor reads"
    let operands := view.getAppArgs
    let subject := operands[operands.size-3]!
    let some parts ← whnfUntil subject ``carried | throwError "expected the physical occupied partition"
    return parts

open Lean Meta Elab Term in
local elab "purchasedPartsQuantities% " paidStx:term ", " rawStx:term ", " dayStx:term : term => do
  let actual := fun (x : Syntax) => do
    let v ← withSynthesize (postpone := .no) <| elabTerm x none
    instantiateMVars v
  let calculation ← actual paidStx
  let nativeReads ← actual rawStx
  let dayProof ← actual dayStx
  let some paid ← whnfUntil calculation ``carried | throwErrorAt paidStx "expected the paid carried partition"
  let physical ← rawPartsInReads nativeReads
  let some (dayTy,paidDate,actualDate) := (← inferType dayProof).consumeMData.eq? | throwError "the paid date equation is missing"
  let current := physical.getAppArgs
  let target := paid.getAppArgs
  let actualQty := current[5]!
  let paidQty := target[5]!
  let qtyTy ← inferType paidQty
  let quantityFamily ← withLocalDeclD `valueDate dayTy fun label => do
    let fields := paidQty.getAppArgs
    let table := fields[3]!
    let tableArgs := table.getAppArgs
    let finalIx := tableArgs.size - 1
    let retimed ← if table.isAppOf ``wideDatedValue then pure (Lean.Expr.proj ``Fin 0 label) else do
      unless table.isAppOf ``wideCorrectedWidths do throwError "the registered width table has no selected stage"
      let succDate := tableArgs[finalIx]!
      unless succDate.isAppOf ``Fin.succ do throwError "the corrected width uses the successor stage"
      pure (mkAppN succDate.getAppFn (succDate.getAppArgs.set! (succDate.getAppNumArgs-1) label))
    let replacement := mkAppN table.getAppFn (tableArgs.set! finalIx retimed)
    mkLambdaFVars #[label] (mkAppN paidQty.getAppFn (fields.set! 3 replacement))
  let eqQty := mkAppN (Lean.mkConst ``selectedQuantityAtDate) #[dayTy,qtyTy,quantityFamily,paidDate,actualDate,dayProof]
  let some positions ← whnfUntil current[8]! ``PacketNeighbor.localSlot | throwError "expected the funded native slot"
  let seatArgs := positions.getAppArgs
  let qtyPos ← match seatArgs.findIdx? (·==actualQty) with
    | some i => pure i
    | none => throwError "the slot lacks its own measured role width"
  let physicalSeatFamily ← withLocalDeclD `roleQuantities qtyTy fun amount =>
    mkLambdaFVars #[amount] (mkAppN positions.getAppFn (seatArgs.set! qtyPos amount))
  let eqSeats := mkAppN (Lean.mkConst ``Hierarchy.Tagged.PassiveWindow.selectedCarriedQuantities)
    #[current[0]!,current[1]!,current[2]!,current[3]!,current[4]!,current[6]!,physicalSeatFamily,
      actualQty,paidQty,eqQty,current[7]!,target[7]!,current[9]!,current[10]!,target[10]!]
  return eqSeats

open Lean Meta Elab Term in
local elab "purchasedNeighborReads% " physicalStx:term ", " sameStx:term : term => do
  let raw ← withSynthesize (postpone := .no) <| elabTerm physicalStx none
  let raw ← instantiateMVars raw
  let equation ← withSynthesize (postpone := .no) <| elabTerm sameStx none
  let equation ← instantiateMVars equation
  let some (partTy,fromParts,toParts) := (← inferType equation).consumeMData.eq? | throwError "expected equal paid partitions"
  forallTelescope (← inferType raw) fun inputs goal => do
    let some view ← whnfUntil goal ``PacketTurns.NeighborReads | throwError "expected occupied reads, got {goal.getAppFn.constName?} with {inputs.size} arguments"
    let args := view.getAppArgs
    let family ← withLocalDeclD `partsAtSite partTy fun parts => do
      let native := mkAppN view.getAppFn (args.set! (args.size-3) parts)
      mkLambdaFVars #[parts] (← mkForallFVars inputs native)
    return mkAppN (Lean.mkConst ``selectedFactAtEqualValue) #[partTy,family,fromParts,toParts,equation,raw]

open Lean Meta Elab Term in
local elab "paidRawSlotWords% " lowBeforeSite:term:arg siteStx:term:arg sideStx:term:arg occupied:term:arg : term => do
  let producer ← withSynthesize (postpone := .no) <| elabTerm lowBeforeSite none
  let site ← withSynthesize (postpone := .no) <| elabTerm siteStx none
  let side ← withSynthesize (postpone := .no) <| elabTerm sideStx (some (Lean.mkConst ``Bool))
  let reads ← withSynthesize (postpone := .no) <| elabTerm occupied none
  let producer ← instantiateMVars producer
  let reads ← instantiateMVars reads
  let parts ← forallTelescopeReducing (← inferType reads) fun parties judgment => do
    let some observed ← whnfUntil judgment ``PacketTurns.NeighborReads
      | throwErrorAt occupied "expected the actual occupied-site neighbor reads"
    let rows := observed.getAppArgs[8]!
    let names := (Lean.collectFVars {} rows).fvarSet
    unless parties.all (fun party => !names.contains party.fvarId!) do
      throwErrorAt occupied "the selected row family depends on the individual occupant"
    pure rows
  let some carriedRows ← whnfUntil parts ``carried | throwErrorAt occupied "expected the carried physical row family"
  let fields := carriedRows.getAppArgs
  unless fields.size == 11 && fields[3]!.isAppOfArity ``Fin 1 do throwErrorAt occupied "unexpected row slot type"
  let positive := mkAppN (Lean.mkConst ``selectedCarriedOwnerPositive) (fields.set! 3 fields[3]!.appArg!)
  let shape := (← whnf (← inferType parts)).getAppArgs
  withLocalDeclD `slotId shape[1]! fun slot => do
    let observed := mkAppN producer #[site,side,shape[2]!,shape[3]!,parts,slot,reads,Lean.mkApp positive slot]
    mkLambdaFVars #[slot] observed
private theorem comparePrintedPartitions {Left Right : Type} (readAt : Left → Right → Prop)
    {physicalLeft purchasedLeft : Left} {physicalRight purchasedRight : Right}
    (eqLeft : physicalLeft = purchasedLeft) (eqRight : physicalRight = purchasedRight)
    (read : readAt physicalLeft physicalRight) : readAt purchasedLeft purchasedRight := by
  cases eqLeft
  cases eqRight
  exact read

open Lean Meta Elab Term in
local elab "purchasedControlPartitions% " observed:term ", " lEq:term ", " rEq:term : term => do
  let actual := fun (e : Syntax) => do
    let proof ← withSynthesize (postpone := .no) <| elabTerm e none
    instantiateMVars proof
  let complete ← actual observed
  let leftEq ← actual lEq
  let rightEq ← actual rEq
  let some (leftTy,physicalLeft,paidLeft) := (← inferType leftEq).consumeMData.eq? | throwError "expected the left paid partition"
  let some (rightTy,physicalRight,paidRight) := (← inferType rightEq).consumeMData.eq? | throwError "expected the right paid partition"
  let some compiled ← whnfUntil (← inferType complete) ``SiteControls.CompiledFields | throwError "expected the signed control observations"
  let fields := compiled.getAppArgs
  let family ← withLocalDeclD `inputPartsAtSite leftTy fun inputPart =>
    withLocalDeclD `offerPartsAtSite rightTy fun offerPart => do
      let updated := (fields.set! (fields.size-4) inputPart).set! (fields.size-3) offerPart
      mkLambdaFVars #[inputPart,offerPart] (mkAppN compiled.getAppFn updated)
  return mkAppN (Lean.mkConst ``comparePrintedPartitions) #[leftTy,rightTy,family,physicalLeft,paidLeft,
    physicalRight,paidRight,leftEq,rightEq,complete]

private theorem atReturnedControlColumns (family : ℕ → ℕ → Prop)
    {eventLow attemptLow eventColumns attemptColumns : ℕ}
    (startEquality : eventLow = attemptLow) (columnEquality : eventColumns = attemptColumns)
    (paidRead : family attemptLow attemptColumns) : family eventLow eventColumns := by
  cases startEquality
  cases columnEquality
  exact paidRead

open Lean Meta Elab Term in
local elab "returnedControlColumns% " measured:term ", " cutEq:term ", " colEq:term : term => do
  let actual := fun (syntaxTerm : Syntax) => do
    let raw ← withSynthesize (postpone := .no) <| elabTerm syntaxTerm none
    let raw ← instantiateMVars raw
    if raw.hasExprMVar then throwErrorAt syntaxTerm "unresolved control-column observation"
    pure raw
  let paidRead ← actual measured
  let startProof ← actual cutEq
  let fieldsProof ← actual colEq
  let some (_,srcCut,dstCut) := (← inferType startProof).eq? | throwErrorAt cutEq "expected the two first signed columns"
  let some (_,srcCount,dstCount) := (← inferType fieldsProof).eq? | throwErrorAt colEq "expected the two column counts"
  let target := (← inferType paidRead).consumeMData.headBeta.consumeMData
  unless target.isAppOf ``SiteControls.CompiledFields do throwErrorAt measured "expected paid compiled field data"
  let operands := target.getAppArgs
  let lowParts := operands.back!.consumeMData
  unless lowParts.isAppOfArity ``SiteControls.lowFieldFrom 5 do throwError "expected a fixed first signed field and stride"
  let fp := lowParts.getAppArgs
  withLocalDeclD `actualCut (Lean.mkConst ``Nat) fun startWord =>
    withLocalDeclD `actualColumnCount (Lean.mkConst ``Nat) fun fieldCount => do
      let physicalLow := mkAppN lowParts.getAppFn ((fp.set! 1 startWord).set! 4 fieldCount)
      let atColumns := mkAppN target.getAppFn (operands.set! (operands.size-1) physicalLow)
      let family ← mkLambdaFVars #[startWord,fieldCount] atColumns
      return mkAppN (Lean.mkConst ``atReturnedControlColumns) #[family,srcCut,dstCut,srcCount,dstCount,startProof,fieldsProof,paidRead]

include routeAge height prices pricePos buy groupsFit metadata lanesFit e perm tag j onDate in
/-- All occupied participants are read on the one real ballot-processing
heap. The control scan then reads that ballot, including every absent slot. -/
abbrev selected_signed_fields (budget : word) (site : Fin S₀) := selectPhysicalFields%
  let facts:=entered
  let dates:=images
  let codes:=key
  let srcWidth:=leftWidth
  let dstWidth:=rightWidth
  let passive:=passiveOf srcWidth
  let wants:=∑i,dmd i
  let offers:=∑i,rewired i
  let l:=inputParts site (passive+wants) srcWidth
  let r':=offerParts site (passive+offers) dstWidth
  let bounds:=nativeRows
  have scalar:=(sector).signed_control_room rankEnd t (rank).room
  have double:=v.signed_double_room h width unitCost a budget
  have sizeFit:=facts.2.2.2.1
  have degreeFit : (g).sites*degree≤2^W := scalar.2.1.le
  have one : 1<2^W := (by decide : 1<2).trans (rank).wide
  have ctrlEarly := selectedPaidSheet% dates, codes, t, control, past
  have ctrlMiddle := selectedPaidSheet% dates, codes, t, control, corrected
  have numbered := codes.2
  let beforeBound := atPhysicalDay% bounds.1, numbered
  let correctedBound := atPhysicalDay% bounds.2, numbered
  let beforeShape := atPhysicalDay% srcWidth, numbered
  let correctedShape := atPhysicalDay% dstWidth, numbered
  let neighbors := v.selected_actual_occupied_ports m ell short u δ ξ unitCost x cpu rate support
    prices pricePos buy groupsFit metadata lanesFit e perm tag j t a onDate height routeAge budget site
  let rawBefore := neighbors.1
  let rawAfter := neighbors.2
  let leftInFundedParts := purchasedPartsQuantities% l, rawBefore, numbered
  let rightInFundedParts := purchasedPartsQuantities% r', rawAfter, numbered
  let paidBefore := purchasedNeighborReads% rawBefore, leftInFundedParts
  let paidAfter := purchasedNeighborReads% rawAfter, rightInFundedParts
  have room:=v.selected_signed_bounds m ell short u δ ξ unitCost x cpu rate support prices pricePos buy
    groupsFit metadata lanesFit e perm tag j height t a onDate site (passive+wants) (passive+offers) srcWidth dstWidth
  have ncols:(g).ballot t=sh:=congrArg (v.widePacketShape h width) onDate
  have ballotRoom := selectedShapeRoom ncols scalar.2.2
  have capacity := selectedDoubleColumns (v.widePacket_low_extent h width a)
  let lowOld := paidRawSlotWords% pack site false rawBefore
  let lowNew := paidRawSlotWords% pack site true rawAfter
  have ids:=(date).signedIdentifiers W scalar.1
  let measured := measuredControlAtPaidSite% ctrlEarly, ctrlMiddle, dates.2.1, site, cap,
    passive, wants, offers, beforeBound, correctedBound, beforeShape, correctedShape,
    ((g).ballotStart sw t), count, heads, capacity, ballotRoom, (v.widePacketLowColumn h width a),
    (v.widePacket_low_column h width a), lowOld, lowNew, one, sizeFit, degreeFit, ids.1, ids.2,
    double, room.1, (fun p : (portGraph S₀).Port site => room.2.1 p.val.1)
  let paidControl := purchasedControlPartitions% measured, leftInFundedParts, rightInFundedParts
  let eventCut := congrArg (v.widePacketLowStart h width) onDate
  let columnCount := congrArg WideCPU.Shape.columns ncols
  let storedControlFields := returnedControlColumns% paidControl, eventCut, columnCount
  have seen:=v.wide_selected_signed_compiled m ell short u δ ξ unitCost x cpu rate support prices pricePos buy
    groupsFit metadata lanesFit e perm tag j t a onDate site (fun p=>passive p.val.1)
    (fun p=>wants p.val.1) (fun p=>offers p.val.1) l r' storedControlFields
  And.intro seen (And.intro paidBefore paidAfter)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
