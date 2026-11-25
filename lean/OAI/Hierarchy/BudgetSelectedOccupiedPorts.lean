import OAI.Hierarchy.TaggedWideFundedSelectedPacket
import OAI.Hierarchy.TaggedWideFundedBallotSnapshots
import OAI.Hierarchy.TaggedWideSelectedSignedWidths
import OAI.Hierarchy.TaggedWideSignedControlRoom
import OAI.Hierarchy.TaggedWideSignedEndpointReads

namespace OAI
noncomputable section
set_option quotPrecheck false
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

local notation "lookup" block:arg participant:arg => columns («D»:=D) n block sites bits (RoleROM.bank rom sites) participant

include oldSheet newSheet strides in
private theorem selected_occupied_role_fields {Ballot : Type*} (location : Ballot → Fin sites)
    (participant : Ballot→Expr) (address : Ballot→Word native)
    (located : ∀party,(participant party).eval m (address party) = ((location party).val : Word native))
    (one : 1<2^native) (siteRoom : sites≤2^native) (spanRoom : sites*D≤2^native)
    (capRoom : cap<2^native) :
    (∀party, location party=s →
      PacketTurns.NeighborReads m (address party) l
        (fun q=>((lookup left (participant party)) q).width)
        (fun q=>((lookup left (participant party)) q).opposite)) ∧
    (∀party, location party=s →
      PacketTurns.NeighborReads m (address party) r
        (fun q=>((lookup right (participant party)) q).width)
        (fun q=>((lookup right (participant party)) q).opposite)) := by
  have atSite (party : Ballot) (hit : location party=s) :
      (participant party).eval m (address party)=(s.val:Word native) :=
    (located party).trans (congrArg (fun num : Fin sites => (num.val:Word native)) hit)
  constructor
  · intro party hit
    exact ports_of_sheet oldSheet strides cap s preBound (rest+want) preShape
      (participant party) (address party) (atSite party hit) one
      (fun i=>(preBound i).trans_lt capRoom) siteRoom spanRoom
  · intro party hit
    exact ports_of_sheet newSheet strides cap s midBound (rest+offer) midShape
      (participant party) (address party) (atSite party hit) one
      (fun i=>(midBound i).trans_lt capRoom) siteRoom spanRoom

end Hierarchy.ProtocolRAM.SiteControls
end

/-! # Occupied parties on the selected signed processing heap -/
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

/- Transport the semantic date of a mounted role field while fixing its address,
heap, and the physical spill input of a corrected sector. -/
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

local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unitCost g
local notation "first" => (lay).pruneScratch+(lay).pruneRows+1
local notation "rankEnd" => v.wideSpillRankEnd h width v.maxBits first
variable (t : Fin (events v.mesh).length) (a : Attempt) (onDate : (events v.mesh).get t=.attempt a)

local notation "extent" => (v.wide_funded_extent h width v.maxBits).trans Sfit
local notation "chosen" => CalendarTape.Prefix.pathVisitAt j t onDate
local notation "reference" => v.wide_reference_date h width S extent perm seed cpu.age cpu.ready.credit
  cpu.ready.size_le (chosen).prior

open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open WideControlJoin WireTelescope.PassMatrix WideCPU
local notation "S₀" => siteLast h d k+1
local notation "R₀" => (reference).2
local notation "age₀" => support.size.tenderAge
local notation "floor₀" => support.size.widthFloor
local notation "sector" => v.wideSpillDates h width ell unitCost v.maxBits first
local notation "dmd" => fun l=>((R₀).row extent age₀ floor₀ l).input
local notation "rewired" => fun l=>((R₀).tender extent age₀ floor₀ l).post ((chosen).choice l)
local notation "degree" => v.widePacketDegree
local notation "cap" => v.wideNeighborCap width unitCost

open HistoryRoles NamedAperture Tagged.PassiveWindow SiteControls WideCPU
local notation "W" => Native.wordBits h d Native.copies
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
local notation "key" => v.selectedPreclipCode m ell short u δ ξ unitCost x cpu perm j t a onDate
local notation "word" => v.PartyWordBounds h width unitCost
local notation "issued" => (R₀).occupiedBallots extent age₀ floor₀

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
local elab "occupiedPortsAtRecordedParty% " data:term,+ : term => do
  let syntaxArgs := data.getElems
  unless syntaxArgs.size == 18 do throwError "expected the dated roles, measured widths, registered party, and numeric bounds"
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
  let embedded := (← inferType xs[12]!).consumeMData
  unless embedded.isAppOfArity ``Function.Embedding 2 do throwError "expected the recorded occupied party embedding"
  let occupantType := embedded.getAppArgs[0]!
  let locationFn := Lean.Expr.proj ``Function.Embedding 0 xs[12]!
  -- The native reader evaluates the descriptor at the recorded word address.
  let partyTriple ← withLocalDeclD `selectedParty occupantType fun party => do
    let candidate := Lean.Expr.proj ``Prod 0 party
    let idx := Lean.Expr.proj ``Subtype 0 candidate
    let eligible := Lean.Expr.proj ``Subtype 1 candidate
    let peer := Lean.Expr.proj ``Prod 1 party
    let mut tagFacts := xs[13]!
    for _ in [0:5] do tagFacts := Lean.Expr.proj ``And 1 tagFacts
    let held := Lean.Expr.proj ``And 1 (mkAppN tagFacts #[idx,eligible,peer])
    let atSiteType ← whnf (← inferType held)
    let some (_, evaluated, _) := atSiteType.eq? | throwError "expected the site read equation from its recorded tag"
    let evalArgs := evaluated.getAppArgs
    unless evalArgs.size ≥ 3 do throwError "incomplete actual party input address"
    pure (← mkLambdaFVars #[party] evalArgs.back!,
      ← mkLambdaFVars #[party] evalArgs[evalArgs.size-2]!, ← mkLambdaFVars #[party] held)
  let args : List (Name × Lean.Expr) := [
    (`h,old[1]!),(`W,old[2]!),(`k,old[3]!),(`attempts,old[4]!),(`N,old[5]!),(`native,old[6]!),
    (`n,old[0]!),(`left,old[13]!),(`right,corrected[13]!),(`depth,old[9]!),(`rom,romBase),
    (`S,old[7]!),(`π,old[8]!),(`mark,old[10]!),(`unique,old[11]!),(`rows,old[12]!),
    (`pre,old[14]!),(`mid,corrected[14]!),(`id,old[15]!),(`m,old[16]!),
    (`oldSheet,xs[0]!),(`newSheet,xs[1]!),(`strides,xs[2]!),(`s,xs[3]!),(`cap,xs[4]!),
    (`rest,xs[5]!),(`want,xs[6]!),(`offer,xs[7]!),(`preBound,xs[8]!),(`midBound,xs[9]!),
    (`preShape,xs[10]!),(`midShape,xs[11]!),(`Ballot,occupantType),(`location,locationFn),
    (`participant,partyTriple.1),(`address,partyTriple.2.1),(`located,partyTriple.2.2),
    (`one,xs[14]!),(`siteRoom,xs[15]!),(`spanRoom,xs[16]!),(`capRoom,xs[17]!)]
  let info ← getConstInfo ``selected_occupied_role_fields
  let fn := Lean.mkConst info.name (info.levelParams.map fun _ => Level.zero)
  forallTelescope (← inferType fn) fun binders _ => do
    let actualArgs ← binders.mapM fun arg => do
      let keyName := (← arg.fvarId!.getDecl).userName.eraseMacroScopes
      let some storedOperand := args.lookup keyName | throwError "unrecognized original occupied-port parameter {keyName}"
      pure storedOperand
    return mkAppN fn actualArgs

include routeAge height prices pricePos buy groupsFit metadata lanesFit e perm tag j onDate in
/-- Every selected party at this site reads its original and corrected neighbors on
the same processing heap. The occupied word determines both width and opposite site. -/
abbrev selected_actual_occupied_ports (budget : word) (site : Fin S₀) := selectPhysicalFields%
  let facts:=entered
  let dates:=images
  let codes:=key
  let srcWidth:=leftWidth
  let dstWidth:=rightWidth
  let passive:=passiveOf srcWidth
  let wants:=∑i,dmd i
  let offers:=∑i,rewired i
  let bounds:=nativeRows
  have scalar:=(sector).signed_control_room rankEnd t (rank).room
  have double:=v.signed_double_room h width unitCost a budget
  have capSmall : cap<2^W := (Nat.le_mul_of_pos_left _ (by decide : 0<2)).trans_lt double
  have sizeFit:=facts.2.2.2.1
  have degreeFit : (g).sites*degree≤2^W := scalar.2.1.le
  have one : 1<2^W := (by decide : 1<2).trans (rank).wide
  have early := selectedPaidSheet% dates, codes, t, processing, past
  have middle := selectedPaidSheet% dates, codes, t, processing, corrected
  have numbered := codes.2
  let loc:=issued
  let beforeBound := atPhysicalDay% bounds.1, numbered
  let correctedBound := atPhysicalDay% bounds.2, numbered
  let beforeShape := atPhysicalDay% srcWidth, numbered
  let correctedShape := atPhysicalDay% dstWidth, numbered
  let neighbors := occupiedPortsAtRecordedParty% early, middle, dates.1.1, site, cap,
    passive, wants, offers, beforeBound, correctedBound, beforeShape, correctedShape,
    loc, facts, one, sizeFit, degreeFit, capSmall
  neighbors

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
