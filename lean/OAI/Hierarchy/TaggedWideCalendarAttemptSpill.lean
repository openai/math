import OAI.Hierarchy.TaggedWideCalendarAttemptAt
import OAI.Hierarchy.TaggedWideCalendarDayOuterBits
import OAI.Hierarchy.TaggedWideRankedSpillCarry
import OAI.Hierarchy.TaggedWideSelectedPreclipReads
import OAI.Hierarchy.TaggedWideSelectedSpillInput
import OAI.Hierarchy.TaggedWideSelectedSignedWidths
import OAI.Hierarchy.TaggedWideCalendarSpillShelfRoom
import OAI.Hierarchy.ProbeFixedFundedAttemptSpill

namespace OAI
/-! # The emitted checked spill comparison at a chosen paid calendar attempt -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open TaggedPrune Tagged.WideControlJoin
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option cleanup.letToHave false
set_option maxRecDepth 12288
set_option maxHeartbeats 2200000
open Lean Elab Term in
local elab "applyRegisteredPost% " original:term " usingPaidPost " purchased:term : term => do
  let carryThroughPre ← withSynthesize (postpone := .no) <| elabTerm original none
  let physicalPost ← withSynthesize (postpone := .no) <| elabTerm purchased none
  return mkApp carryThroughPre physicalPost

section
open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
open LinearAlgebra.SpectralBooks ChordGraph

private theorem spillValueOnNumberedVertex {h W k attempts : Nat} (S : PurchaseSampler)
    (vtx : Site h (2^W) k) {F : Sort _}
    (valueOn : (vertex : Site h (2^W) k) →
      (Fiber (attempts:=attempts) S vertex → Fin (stride k S.degree attempts)) → F) :
    valueOn vtx (DatedSpillOffsets.spillSeat S vtx) =
      valueOn ((siteNumber h (2^W) k).symm ((siteNumber h (2^W) k) vtx))
        (fun a => (finProdFinEquiv.symm (shelfSlot (attempts:=attempts) S a.val)).2) := by
  rw [Equiv.symm_apply_apply]
  apply congrArg (valueOn vtx)
  funext a
  change DatedSpillOffsets.spillSeat S vtx a = (finProdFinEquiv.symm (finProdFinEquiv _)).2
  rw [Equiv.symm_apply_apply]
  rfl
end

open Lean Elab Tactic Meta in
local elab "usePhysicalVertexRow" : tactic => withMainContext do
  let gm ← getMainGoal
  let some (α, lhs, rhs) := (← gm.getType).eq? | throwError "expected the original scalar comparison"
  let netName := ``WireTelescope.PassMatrix.spillRow
  let validate (val : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
    unless val.getAppFn.constName?.any (fun n=>n.getString!=="value") do throwError "expected original physical valuation"
    let args := val.getAppArgs
    let net := args[args.size-2]!
    let some row ← whnfUntil net netName | throwError "expected original physical spillRow {net.getAppFn.constName?}"
    return (val,row)
  let (value, row) ← validate lhs
  let _ ← validate rhs
  let original := row.getAppArgs
  let info ← getConstInfo netName
  let mut ty := info.type
  let mut names := #[]
  for _ in [:original.size] do
    names := names.push ty.bindingName!
    ty := ty.bindingBody!
  let handle := fun (nm : Name) => names.idxOf nm
  let s := original[handle `S]!
  let vertex := original[handle `vtx]!
  let role := original[handle `roleRoom]!
  let oldSeat := original[handle `seat]!
  let replaceVertex (term alt : Lean.Expr) : Lean.Expr :=
    term.replace fun node=>if node==vertex then some alt else none
  let family ← withLocalDeclD `rowVertex (← inferType vertex) fun vtx => do
    withLocalDeclD `rowSeat (replaceVertex (← inferType oldSeat) vtx) fun seat => do
      let revised := ((original.set! (handle `vtx) vtx).set! (handle `roleRoom) (replaceVertex role vtx)).set! (handle `seat) seat
      let net := mkAppN row.getAppFn revised
      let userArgs := value.getAppArgs
      mkLambdaFVars #[vtx,seat] (mkAppN value.getAppFn (userArgs.set! (userArgs.size-2) net))
  let bridge := mkConst ``spillValueOnNumberedVertex [← getLevel α]
  let proof := mkAppN bridge #[original[handle `h]!,original[handle `wr]!,original[handle `k]!,original[handle `attempts]!,s,vertex,α,family]
  gm.assign proof
  replaceMainGoal []


-- Use the original two dependent read types as the Boolean recursor's branches.
open Lean Meta Elab Tactic in
local elab "splitPaidReadSides" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let actualType ← instantiateMVars (← goal.getType)
    let exposed ← if actualType.consumeMData.isForall then pure actualType.consumeMData else whnf actualType
    let .forallE side sideType reading info := exposed
      | throwError "expected the registered bit-reader's Boolean argument"
    unless sideType.isConstOf ``Bool do throwError "expected a Boolean side"
    let motive := Lean.Expr.lam side sideType reading info
    let first ← mkFreshExprSyntheticOpaqueMVar (reading.instantiate1 (Lean.mkConst ``Bool.false))
    let next ← mkFreshExprSyntheticOpaqueMVar (reading.instantiate1 (Lean.mkConst ``Bool.true))
    goal.assign (mkApp3 (Lean.mkConst ``Bool.rec [.zero]) motive first next)
    replaceMainGoal [first.mvarId!, next.mvarId!]

open Lean Elab Tactic Meta in
local elab "finishRegisteredSpill " physical:term " through " transfer:term : tactic => do
  let target ← getMainGoal
  target.withContext do
    let first ← Term.elabTermAndSynthesize physical none
    let second ← Term.elabTermAndSynthesize transfer none
    let some (carrier, lhs, middle) := (← whnf (← inferType first)).eq?
      | throwError "expected the physical spill matrix equality"
    let some (_, _, rhs) := (← whnf (← inferType second)).eq?
      | throwError "expected the original transfer matrix equality"
    let some (_, wanted, _) := (← whnf (← target.getType)).eq?
      | throwError "expected the funded calendar equation"
    let level ← getLevel carrier
    let trans := mkConst ``Eq.trans [level]
    let row ← mkFreshExprSyntheticOpaqueMVar (mkApp3 (mkConst ``Eq [level]) carrier lhs wanted)
    let reversed := mkAppN (mkConst ``Eq.symm [level]) #[carrier, lhs, wanted, row]
    let paid := mkAppN trans #[carrier, lhs, middle, rhs, first, second]
    target.assign (mkAppN trans #[carrier, wanted, lhs, rhs, reversed, paid])
    replaceMainGoal [row.mvarId!]

open Lean Elab Term Meta in
local elab "paidRankedPostPartitions% " rankTerm:term " usingRankUpper " upperTerm:term " usingRankPostEq " postWidthTerm:term
    " usingRankPaidRead " paidReadTerm:term : term => do
  let rank ← withSynthesize (postpone := .no) <| elabTerm rankTerm none
  let upper ← withSynthesize (postpone := .no) <| elabTerm upperTerm none
  let post ← withSynthesize (postpone := .no) <| elabTerm postWidthTerm none
  let paid ← withSynthesize (postpone := .no) <| elabTerm paidReadTerm none
  let mut rest ← inferType rank
  let mut scopeNames := #[]
  let mut nativePart : Option Lean.Expr := none
  for _ in [:120] do
    match rest.consumeMData with
    | .forallE n _ next _ =>
      scopeNames := scopeNames.push n
      rest := next
    | .letE n _ value next _ =>
      if n == `rightParts then
        let mut vals := #[]
        for i in [:scopeNames.size] do
          let nm := scopeNames[i]!
          let v ← if value.hasLooseBVar (scopeNames.size-1-i) then do
            if [`postBound,`high].contains nm then pure upper
            else if [`postShape,`postEq].contains nm then pure post
            else throwError "additional native positive partition field {nm}"
          else pure (.sort .zero)
          vals := vals.push v
        nativePart := some (value.instantiateRev vals)
        break
      scopeNames := scopeNames.push n
      rest := next
    | _ => throwError "expected native rightParts after {scopeNames}"
  let some parts := nativePart | throwError "no registered positive role partitions"
  let .letE _ _ paidPart _ _ := (← inferType paid).consumeMData
    | throwError "expected purchased carried rows"
  mkEq paidPart parts

open Lean Elab Term Meta in
local elab "positivePartitionRefl" : term <= expected => do
  let some (_,lhs,_) := (← whnf expected).eq? | throwError "expected two actual terminal role partitions"
  mkEqRefl lhs

private theorem originalPaidAttemptMarker {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (h width ell unitCost bits rankFirst : ℕ)
    {date : Fin (events v.mesh).length} {a : Attempt}
    (day : (events v.mesh).get date = .attempt a) :
    (v.wideSpillDates h width ell unitCost bits rankFirst).attempt date = true := by
  change (match (events v.mesh).get date with
    | .attempt _ => true
    | .feed _ => false) = true
  rw [day]

private theorem calendarCheckoutAtCode {Code Cell : Type} (readAt : Code → ℕ → Cell)
    {chosen printed : Code} {limit : ℕ} {image : ℕ → Cell} (sameCode : chosen = printed)
    (stored : ∀ n < limit, image n = readAt printed n) : ∀ n < limit, image n = readAt chosen n := by
  cases sameCode
  exact stored

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
open scoped Classical Fin.CommRing
open private preclipSiteFormula selectedPreclipSiteOnNamedLayout from OAI.Hierarchy.TaggedWideCalendarAttemptAt

/-- Restrict a paid layout to one site before specializing the dated widths. -/
private def paidReadSiteChart {siteCount laneCount : Nat} {bitAt : Fin siteCount → Type}
    {paidLayout : Sigma bitAt ↪ Fin siteCount × Fin laneCount}
    (paidSite : preclipSiteFormula (Fin siteCount) bitAt (Fin laneCount) paidLayout)
    (siteId : Fin siteCount) : bitAt siteId ↪ Fin laneCount :=
  LedgerStep.siteChart paidLayout paidSite siteId

section
open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.BranchRoles Tagged.WideCalendarSites
open ThreeFlat Routing
open LinearAlgebra.SpectralBooks ChordGraph
open Tagged.WideStack.Leaf ProtocolRAMReportedPorts
open private selectedPlacementBodyEq from OAI.Hierarchy.TaggedWideCalendarAttemptAt

-- Keep the raw indexed proof and the captured named site law as independent
-- arguments. Only the physical embeddings determine the middle gate.
private theorem fundedReadOnPaidMiddle {K N : ℕ} {B : Widths K}
    (indexed selected : (Σ s, SiteBit B s) ↪ Fin K × Fin N)
    (indexedSite : ∀ s (u : SiteBit B s), (indexed ⟨s,u⟩).1 = s)
    (paidSite : preclipSiteFormula (Fin K) (SiteBit B) (Fin N) selected)
    (s : Fin K) (z : State B s) (alignment : indexed = selected)
    (P : (Fin N → Bool) → Prop)
    (read : P (LedgerStep.middle s (LedgerStep.siteChart indexed indexedSite s) z)) :
    P (LedgerStep.middle s (paidReadSiteChart paidSite s) z) := by
  have columns (u : SiteBit B s) : (indexed ⟨s,u⟩).2 = (selected ⟨s,u⟩).2 :=
    congrArg (fun (layout : (Σ s, SiteBit B s) ↪ Fin K × Fin N) => (layout ⟨s,u⟩).2) alignment
  have sameChart : LedgerStep.siteChart indexed indexedSite s = paidReadSiteChart paidSite s :=
    Function.Embedding.ext columns
  exact (congrArg (fun chart => P (LedgerStep.middle s chart z)) sameChart).mp read

open Lean Elab Term Meta in
private partial def fundedGateMiddle (term : Lean.Expr) (replaceWith : Option Lean.Expr) :
    Option Lean.Expr := Id.run do
  if term.isAppOfArity ``LedgerStep.middle 6 then return some (replaceWith.getD term)
  unless term.isAppOfArity ``Sum.elim 5 do return none
  let args := term.getAppArgs
  for i in #[3,4] do
    if let some child := fundedGateMiddle args[i]! replaceWith then
      return some (if replaceWith.isSome then mkAppN term.getAppFn (args.set! i child) else child)
  return none

open Lean Elab Term Meta in
private def movePaidReading (observed next : Lean.Expr) : TermElabM Lean.Expr := do
  let sourceTy := (← inferType observed).consumeMData
  let .letE p pt pv state pb := sourceTy | throwError "expected the signed partition"
  let .letE y yt yv gate yb := state | throwError "expected the transported paid state"
  let .letE g gt gv rows gb := gate | throwError "expected the signed gate"
  let some old := fundedGateMiddle gv none | throwError "expected the funded site gate"
  unless next.isAppOfArity ``LedgerStep.middle 6 do throwError "expected the named site middle"
  let #[siteCount0,laneCount0,earnedWidths0,partySite0,oldChart,state0] := old.getAppArgs | throwError "expected the dated state"
  let newChart := next.getAppArgs[4]!
  unless oldChart.isAppOfArity ``LedgerStep.siteChart 6 && newChart.isAppOfArity ``paidReadSiteChart 6 do
    throwError "expected the original site chart and its paid counterpart"
  let oldArgs := oldChart.getAppArgs
  let nextArgs := newChart.getAppArgs
  let namedLayout := nextArgs[3]!
  unless namedLayout.isAppOf ``selected_preclip_layout do throwError "expected the selected original placement"
  -- The selected embedding is the dependent application of the very same funded lower producer.
  let mut alignment ← mkConstWithFreshMVarLevels ``selectedPlacementBodyEq
  for arg in namedLayout.getAppArgs do
    alignment ← mkCongrFun alignment arg
  withLocalDeclD `gateMiddle (← inferType old) fun middleValue => do
    let some updated := fundedGateMiddle gv (some middleValue) | throwError "expected the funded gate aperture"
    let prop := Expr.letE p pt pv (.letE y yt yv (.letE g gt updated rows gb) yb) pb
    let predicate ← mkLambdaFVars #[middleValue] prop
    return mkAppN (mkConst ``fundedReadOnPaidMiddle) #[siteCount0,laneCount0,earnedWidths0,oldArgs[3]!,namedLayout,
      oldArgs[4]!,nextArgs[4]!,partySite0,state0,alignment,predicate,observed]


open Lean Elab Term Meta in
private meta def originalOfferProof : TermElabM Lean.Expr := do
  let source ← getConstInfo ``calendar_day_offer_read
  forallBoundedTelescope source.type (some 45) fun args residual => do
    unless args.size == 45 do throwError "expected the full original chronological offer reading"
    let paid := mkAppN (mkConst source.name) args
    let .letE p pt pv (.letE y yt yv (.letE g gt gv rows gb) yb) pb := residual.consumeMData
      | throwError "expected the original carrying partition, transported state and gate values"
    let some old := fundedGateMiddle gv none | throwError "expected the dated offer's funded middle"
    let chart := old.getAppArgs[4]!
    let original := (source.value!.beta (args.extract 0 42)).consumeMData
    unless original.isAppOf ``selected_offer_read && original.getAppArgs.back? == some args[41]! do
      throwError "expected the selected offer through clipSide"
    let physical := original.getAppArgs.extract 0 40
    let layout := mkAppN (mkConst ``selected_preclip_layout) physical
    let siteLaw := mkAppN (mkConst ``selectedPreclipSiteOnNamedLayout) physical
    let nextChart := mkAppN (mkConst ``paidReadSiteChart) ((chart.getAppArgs.set! 3 layout).set! 4 siteLaw)
    let next := mkAppN old.getAppFn (old.getAppArgs.set! 4 nextChart)
    let bridge ← movePaidReading paid next
    let some newGate := fundedGateMiddle gv (some next) | throwError "expected one dated middle in the physical offer"
    let target := Expr.letE p pt pv (.letE y yt yv (.letE g gt newGate rows gb) yb) pb
    mkLambdaFVars args (mkApp2 (mkConst ``_root_.id [.zero]) target bridge)

open Lean Elab Term in
local elab "originalOfferOnPaidChart%" : term => originalOfferProof

open Lean Elab Term Meta in
local elab "originalOfferOnPaidChartType%" : term => do
  inferType (← originalOfferProof)

private theorem originalOfferOnPaidChart : originalOfferOnPaidChartType% :=
  no_implicit_lambda% originalOfferOnPaidChart%

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun suggestionSuffixes => "originalOfferOnPaidChart" :: suggestionSuffixes

end

open Lean Elab Term Meta in
local elab "paidReadSiteChart% " paidTerm:term " atSite " siteExpr:term : term => do
  let paid ← withSynthesize (postpone := .no) <| elabTerm paidTerm none
  let some paidType ← whnfUntil (← inferType paid) ``preclipSiteFormula
    | throwErrorAt paidTerm "expected a site law for the paid layout"
  let #[physicalSites, bitAt, physicalLanes, paidLayout] := paidType.getAppArgs
    | throwErrorAt paidTerm "expected a site family and lane family"
  let some siteFin ← whnfUntil physicalSites ``Fin | throwError "expected the finite physical site count"
  let some laneFin ← whnfUntil physicalLanes ``Fin | throwError "expected the finite physical lane count"
  return mkAppN (← mkConstWithFreshMVarLevels ``paidReadSiteChart)
    #[siteFin.appArg!, laneFin.appArg!, bitAt, paidLayout, paid, ← elabTerm siteExpr none]

open Lean Elab Term Meta in
local elab "applyCalendarLayoutOperand% " producer:ident "[" values:term,* "]" : term => do
  let format ← getFVarFromUserName `v
  let some formatType ← whnfUntil (← inferType format) ``FixedProtocolFormat
    | throwError "expected the dated protocol format"
  let name ← resolveGlobalConstNoOverload producer
  let mut fn := mkAppN (← mkConstWithFreshMVarLevels name) formatType.getAppArgs
  for value in values.getElems do fn := mkApp fn (← elabTerm value none)
  return fn

section
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "page" => v.wideSignedPage h width
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "stock" => v.fixedTerminalStock P h width
local notation "bits" => page stock
local notation "banks" => TerminalLayout.settlement bits stock
local notation "source" => TerminalLayout.source bits
local notation "table" => TerminalLayout.table bits
local notation "target" => TerminalLayout.destination bits
variable (size : ℕ) (π : Equiv.Perm (Fin (2^h)))
  (seed : Boot.Tape h D) (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "reader" => v.wideSelector h width age budget small
local notation "es" => events v.mesh
local notation "L" => (reader).format.windows
local notation "origin" b:arg => v.wideOrigin h width size ((L).header es b seed) π
local notation "slots" => (reader).format.slot
open Filter CalendarTape RepairHistogram HistoryRoles.RoleProgram ProtocolRAMEmit
open LinearAlgebra.SpectralBooks ChordGraph
namespace FundedDate
open HistoryRoles
variable {v h width size π seed age budget small}

open private preclipEntriesAt from OAI.Hierarchy.TaggedWireFundedPreclipWidth

private abbrev selectedPreclipIssueTableAt (code : Bits (CalendarTape.bits slots es))
    (expense : v.wideFundedSize h width v.maxBits ≤ size) (ledger : v.wideDatedLedgerHeight ≤ h) :=
  preclipEntriesAt (v:=v) («h»:=h) («width»:=width) («size»:=size) (π:=π)
    ((L).header es code seed) expense ledger small budget (0 : Word w)

private def rankedPreclipPinsAt (first : ℕ) (input : Fin (es).length → Memory w)
    (code : Bits (CalendarTape.bits slots es)) (day : Fin (es).length)
    (issues : Attempt → Entry num width) (cap : ℕ) (expected : Widths (siteLast h D k + 1)) : Prop :=
  let raw := (L).header es code seed
  let marks := v.birthMarks P h width r banks source table target owners (origin code)
  let rowOrder := v.wideOrder h width
  let cardRows := v.wide_dated_bought_rows h width
  let names := timeRows v.sampler π.symm v.depth marks (P).catalogue rowOrder cardRows (pairKeys (Columns h D) k)
  let embedded := DatedRows.embed v.sampler π.symm v.depth marks (P).catalogue rowOrder cardRows
  let corrected := v.wideCorrectedWidths h width size v.radius π.symm raw v.maxBits issues first input
  let qty := corrected 0 day.succ ∘ embedded ∘ names
  (∀ i, qty i ≤ cap) ∧
    installedWidths (HistoryRoles.sorted v.sampler π.symm v.depth marks ∘ names) qty = expected

private def selectedPreclipPartsForCode (first : ℕ) (input : Fin (es).length → Memory w)
    (cap : ℕ) (widthAtSite : Widths (siteLast h D k + 1)) (siteIndex : Fin (siteLast h D k + 1))
    (code : Bits (CalendarTape.bits slots es)) (dayIndex : Fin (es).length) (issued : Attempt → Entry num width) :=
  let raw := (L).header es code seed
  let marks := v.birthMarks P h width r banks source table target owners (origin code)
  let rowOrder := v.wideOrder h width
  let cardRows := v.wide_dated_bought_rows h width
  let names := timeRows v.sampler π.symm v.depth marks (P).catalogue rowOrder cardRows (pairKeys (Columns h D) k)
  let embedded := DatedRows.embed v.sampler π.symm v.depth marks (P).catalogue rowOrder cardRows
  let corrected := v.wideCorrectedWidths h width size v.radius π.symm raw v.maxBits issued first input
  let qty := corrected 0 dayIndex.succ ∘ embedded ∘ names
  let ends := HistoryRoles.sorted v.sampler π.symm v.depth marks ∘ names
  fun (exclusive : Exclusive marks) (fits : ∀ idx, qty idx ≤ cap)
      (widthEq : installedWidths ends qty = widthAtSite) =>
    PassiveWindow.carried ends qty siteIndex fits
      (PacketNeighbor.localSlot ends qty (named v.sampler π.symm v.depth marks exclusive names)
        (shelfSlot v.sampler) (named_coordinate v.sampler π.symm v.depth marks exclusive names) siteIndex)
      widthEq

section
private theorem selectedPreclipCarryingAtKey {Code Day Table Partition : Type}
    (ExclusiveAt : Code → Prop) (Fits Shape : Code → Day → Table → Prop)
    (make : ∀ c d entries, ExclusiveAt c → Fits c d entries → Shape c d entries → Partition)
    (issuedAt : Code → Table) {chosen printed : Code} {pathDay currentDay : Day} {registered : Table}
    (hCode : chosen = printed) (hDate : pathDay = currentDay) (hTable : registered = issuedAt printed)
    (chosenExclusive : ExclusiveAt chosen) (printedExclusive : ExclusiveAt printed)
    (chosenFit : Fits chosen pathDay (issuedAt chosen)) (printedFit : Fits printed currentDay registered)
    (chosenShape : Shape chosen pathDay (issuedAt chosen)) (printedShape : Shape printed currentDay registered) :
    make chosen pathDay (issuedAt chosen) chosenExclusive chosenFit chosenShape =
      make printed currentDay registered printedExclusive printedFit printedShape := by
  cases hCode
  cases hDate
  cases hTable
  rfl

open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.ChordGraph
open AdaptiveProbe Tagged PassiveWindow WireTelescope

private theorem selectedPreclipCarryingAtAttempt {rowCount siteCount degree cap : ℕ}
    (ends : Fin rowCount → Chord siteCount) (funded original : Fin rowCount → ℕ)
    (site : Fin siteCount) (total : Widths siteCount)
    (slotAt : ∀ quantities, EndsAt ends quantities site ↪ Fin degree)
    {flag : Bool} (atAttempt : flag = true)
    (fundedFit : ∀ row, funded row ≤ cap) (fundedWidth : installedWidths ends funded = total)
    (attemptFit : ∀ row, (if flag then funded else original) row ≤ cap)
    (attemptWidth : installedWidths ends (if flag then funded else original) = total) :
    carried ends funded site fundedFit (slotAt funded) fundedWidth =
      carried ends (if flag then funded else original) site attemptFit
        (slotAt (if flag then funded else original)) attemptWidth := by
  subst flag
  rfl

open Lean Meta in
private def carriedFieldNamed (expression : Lean.Expr) (head : Name) (binder : Name) : MetaM Lean.Expr := do
  let some application ← whnfUntil expression head
    | throwError "expected {head}, found {expression.getAppFn.constName?}"
  let mut ty := (← getConstInfo head).type
  for argument in application.getAppArgs do
    let .forallE name _ rest _ := ty | break
    if name == binder then return argument
    ty := rest
  throwError "{head} lacks {binder}"

open Lean Meta in
private def makePaidApertureEquality
    (offeredParts rankedParts rowCode tableAt issued key atAttempt pins : Lean.Expr) : MetaM Lean.Expr := do
  let partition ← inferType offeredParts
  let project (x : Lean.Expr) (binder : Name) := carriedFieldNamed x ``PassiveWindow.carried binder
  let fundedSocket ← project offeredParts `slot
  let rankedSocket ← project rankedParts `slot
  let getExclusive (socket : Lean.Expr) := do
    let physicalPorts ← carriedFieldNamed socket ``PacketNeighbor.localSlot `port
    carriedFieldNamed physicalPorts ``HistoryRoles.named `unique
  let leftExclusive ← getExclusive fundedSocket
  let rightExclusive ← getExclusive rankedSocket
  let leftBound ← project offeredParts `room
  let leftShape ← project offeredParts `shape
  let rightBound ← project rankedParts `room
  let rightShape ← project rankedParts `shape
  let rhsQty ← project rankedParts `bits
  let some conditional ← whnfUntil rhsQty ``ite | throwError "expected the selected rank's conditional quantities"
  let conditionalArgs := conditional.getAppArgs
  let corrected := conditionalArgs[conditionalArgs.size - 2]!
  let uncorrected := conditionalArgs.back!
  let hCode := Lean.Expr.proj ``And 0 key
  let hDay := Lean.Expr.proj ``And 1 key
  let some (codeType, chosen, printed) := (← whnf (← inferType hCode)).eq? | throwError "expected the recorded code"
  let some (dayType, originalDay, daily) := (← whnf (← inferType hDay)).eq? | throwError "expected the recorded date"
  let some (_, flag, _) := (← whnf (← inferType atAttempt)).eq? | throwError "expected a paid attempt"
  let fit := Lean.Expr.proj ``And 0 pins
  let widthEq := Lean.Expr.proj ``And 1 pins
  let (exclusiveAt, fitAt, shapeAt) ← forallBoundedTelescope (← inferType rowCode) (some 3) fun idx tail =>
    forallBoundedTelescope tail (some 3) fun properties _ => do
      unless idx.size == 3 && properties.size == 3 do throwError "unexpected physical aperture specification"
      return (← mkLambdaFVars #[idx[0]!] (← inferType properties[0]!),
        ← mkLambdaFVars idx (← inferType properties[1]!), ← mkLambdaFVars idx (← inferType properties[2]!))
  let keyProof := mkAppN (Lean.mkConst ``selectedPreclipCarryingAtKey)
    #[codeType, dayType, ← inferType issued, partition, exclusiveAt, fitAt, shapeAt, rowCode,
      tableAt, chosen, printed, originalDay, daily, issued, hCode, hDay, ← mkEqRefl issued,
      leftExclusive, rightExclusive, leftBound, fit, leftShape, widthEq]
  let active := mkAppN rowCode #[printed, daily, issued, rightExclusive, fit, widthEq]
  let some atSlot ← whnfUntil rankedSocket ``PacketNeighbor.localSlot | throwError "registered local socket is absent"
  let mut slotType := (← getConstInfo ``PacketNeighbor.localSlot).type
  let slotArgs := atSlot.getAppArgs
  let mut bitIdx := none
  for k in [:slotArgs.size] do
    if slotType.bindingName! == `bits then bitIdx := some k
    slotType := slotType.bindingBody!
  let some bitIndex := bitIdx | throwError "physical socket lacks quantities"
  let family ← withLocalDeclD `quantities (← inferType corrected) fun quantity =>
    mkLambdaFVars #[quantity] (mkAppN atSlot.getAppFn (slotArgs.set! bitIndex quantity))
  let lowerWidth := (← project rankedParts `A).getAppArgs.back!
  let atFlagProof := mkAppN (Lean.mkConst ``selectedPreclipCarryingAtAttempt)
    #[← project rankedParts `n, ← project rankedParts `S, lowerWidth, ← project rankedParts `cap,
      ← project rankedParts `ends, corrected, uncorrected, ← project rankedParts `s, ← project rankedParts `total,
      family, flag, atAttempt, fit, widthEq, rightBound, rightShape]
  return mkAppN (Lean.mkConst ``Eq.trans [← getLevel partition])
    #[partition, offeredParts, active, rankedParts, keyProof, atFlagProof]

end

private theorem transferPrintedPins {Code Day Entries : Type} (property : Code → Day → Entries → Prop)
    (entries : Code → Entries) {chosen printed : Code} {selectedDay daily : Day} {issued : Entries}
    (hc : chosen=printed) (hd : selectedDay=daily) (he : issued=entries printed)
    (selected : property chosen selectedDay (entries chosen)) : property printed daily issued := by
  cases hc
  cases hd
  cases he
  exact selected

end FundedDate
end

private theorem forActualSite {X Y : Type*} (e : X ≃ Y) (P : Y → Prop)
    (prove : ∀ vtx, P (e vtx)) (numberedCell : Y) : P numberedCell :=
  e.apply_symm_apply numberedCell ▸ prove (e.symm numberedCell)

section
open Tagged.WideControlJoin
private theorem postTap_same_memory {R D Ex Sel : Type} [Fintype R]
    (gate_ : Gate) {K deg channelCap : ℕ} (events_ : List Event) (roleRoom : R → ℕ) (roleSlots : R ↪ Fin (K*deg))
    (dateWire : Fin ((events_.length+1)*Fintype.card ((r:R)×Fin (roleRoom r))) → D)
    (j : Fin events_.length) (siteId : Fin K) (ext : Ex→Bool) (sel : Sel→Bool) (dataBank : D→Bool)
    (middleBank : Fin (deg*channelCap)→Bool) (mem1 mem2 : Memory gate_.W) (column : Fin deg) (bit : Fin channelCap) :
    Sum.elim (Sum.elim ext (Sum.elim sel (Sum.elim (Sum.elim dataBank middleBank) (gate_.terminal mem1))))
      id (LedgerStep.substepWord gate_ events_ roleRoom roleSlots dateWire j siteId true true column bit) =
    Sum.elim (Sum.elim ext (Sum.elim sel (Sum.elim (Sum.elim dataBank middleBank) (gate_.terminal mem2))))
      id (LedgerStep.substepWord gate_ events_ roleRoom roleSlots dateWire j siteId true true column bit) := by
  simp only [LedgerStep.substepWord]
  cases datedRole events_ roleRoom roleSlots dateWire j siteId true column bit.val <;> rfl
private theorem postTap_same_memory_at_capped_digit {R D Ex Sel : Type} [Fintype R]
    (gate_ : Gate) {K deg channelCap : ℕ} (events_ : List Event) (roleRoom : R → ℕ) (roleSlots : R ↪ Fin (K*deg))
    (dateWire : Fin ((events_.length+1)*Fintype.card ((r:R)×Fin (roleRoom r))) → D)
    (j : Fin events_.length) (siteId : Fin K) (ext : Ex→Bool) (sel : Sel→Bool) (dataBank : D→Bool)
    (middleBank : Fin (deg*channelCap)→Bool) (mem1 mem2 : Memory gate_.W) (column : Fin deg) (firstBit nextBit : Fin channelCap) (sameDigit : firstBit.val = nextBit.val) :
    Sum.elim (Sum.elim ext (Sum.elim sel (Sum.elim (Sum.elim dataBank middleBank) (gate_.terminal mem1))))
      id (LedgerStep.substepWord gate_ events_ roleRoom roleSlots dateWire j siteId true true column firstBit) =
    Sum.elim (Sum.elim ext (Sum.elim sel (Sum.elim (Sum.elim dataBank middleBank) (gate_.terminal mem2))))
      id (LedgerStep.substepWord gate_ events_ roleRoom roleSlots dateWire j siteId true true column nextBit) := by
  refine (postTap_same_memory gate_ events_ roleRoom roleSlots dateWire j siteId ext sel dataBank middleBank
    mem1 mem2 column firstBit).trans ?_
  exact congrArg (fun capped : Fin channelCap =>
    Sum.elim (Sum.elim ext (Sum.elim sel (Sum.elim (Sum.elim dataBank middleBank) (gate_.terminal mem2)))) id
      (LedgerStep.substepWord gate_ events_ roleRoom roleSlots dateWire j siteId true true column capped))
    (Fin.ext sameDigit)

end

open Lean Elab Tactic Meta in
local elab "closePositivePost " physical:ident column:ident neighbor:ident occupied:ident digit:ident : tactic =>
  withMainContext do
    let main ← getMainGoal
    let paid := mkAppN (← getFVarFromUserName physical.getId) (← #[column,neighbor,occupied,digit].mapM (getFVarFromUserName ·.getId))
    let some (α, lhs, rhs) := (← whnf (← main.getType)).eq? | throwError "expected a registered bit equation"
    let some (_, paidLhs, _) := (← whnf (← inferType paid)).eq? | throwError "expected a purchased post bit"
    let view (e : Lean.Expr) (nm : Name) : MetaM Lean.Expr := do
      let simple := e.consumeMData.headBeta
      if simple.isAppOf nm then return simple
      let some exposedHead ← whnfUntil simple nm | throwError "expected {nm}, got {simple.getAppFn.constName?}"
      return exposedHead
    let banks (sum : Lean.Expr) : MetaM (Array Lean.Expr) := do
      let ev ← view sum ``Sum.elim
      let value ← view ev.getAppArgs[ev.getAppNumArgs - 3]! ``Sum.elim
      let sel ← view value.getAppArgs.back! ``Sum.elim
      let dat ← view sel.getAppArgs.back! ``Sum.elim
      let augmented ← view dat.getAppArgs[dat.getAppNumArgs - 2]! ``Sum.elim
      let term ← view dat.getAppArgs.back! ``Gate.terminal
      return #[value.getAppArgs[value.getAppNumArgs - 2]!,sel.getAppArgs[sel.getAppNumArgs - 2]!,
        augmented.getAppArgs[augmented.getAppNumArgs - 2]!,augmented.getAppArgs.back!,term.getAppArgs.back!]
    let tap ← view (← view lhs ``Sum.elim).getAppArgs.back! ``LedgerStep.substepWord
    let args := tap.getAppArgs
    let original ← banks lhs
    let chosen ← banks paidLhs
    let paidTap ← view (← view paidLhs ``Sum.elim).getAppArgs.back! ``LedgerStep.substepWord
    let boundedDigit ← getFVarFromUserName digit.getId
    let sameDigit ← mkEqRefl (Lean.Expr.proj ``Fin 0 boundedDigit)
    let terminalProof := mkAppN (← mkConstWithFreshMVarLevels ``postTap_same_memory_at_capped_digit)
      (args.extract 0 (args.size - 4) ++ original ++ #[chosen.back!,args[args.size - 2]!,args.back!,
        paidTap.getAppArgs.back!,sameDigit])
    let equal := mkConst ``Eq.trans [Lean.Level.succ Lean.Level.zero]
    main.assign (mkAppN equal #[α,lhs,paidLhs,rhs,terminalProof,paid])
    replaceMainGoal []

open Lean Elab Tactic Meta in
local elab "compareOriginalPositiveTaps" : tactic => do
  let (localArgs,main) ← (← getMainGoal).intros
  unless localArgs.size ≥ 4 do throwError "expected original physical read binders"
  replaceMainGoal [main]
  withMainContext do
    let some (_,lhs,paidLhs) := (← whnf (← main.getType)).eq? | throwError "expected the original two valuations"
    let view (e : Lean.Expr) (nm : Name) : MetaM Lean.Expr := do
      let simple := e.consumeMData.headBeta
      if simple.isAppOf nm then return simple
      let some exposedHead ← whnfUntil simple nm | throwError "expected {nm}, got {simple.getAppFn.constName?}"
      return exposedHead
    let banks (sum : Lean.Expr) : MetaM (Array Lean.Expr) := do
      let ev ← view sum ``Sum.elim
      let value ← view ev.getAppArgs[ev.getAppNumArgs - 3]! ``Sum.elim
      let sel ← view value.getAppArgs.back! ``Sum.elim
      let dat ← view sel.getAppArgs.back! ``Sum.elim
      let augmented ← view dat.getAppArgs[dat.getAppNumArgs - 2]! ``Sum.elim
      let term ← view dat.getAppArgs.back! ``Gate.terminal
      return #[value.getAppArgs[value.getAppNumArgs - 2]!,sel.getAppArgs[sel.getAppNumArgs - 2]!,
        augmented.getAppArgs[augmented.getAppNumArgs - 2]!,augmented.getAppArgs.back!,term.getAppArgs.back!]
    let tap ← view (← view lhs ``Sum.elim).getAppArgs.back! ``LedgerStep.substepWord
    let args := tap.getAppArgs
    let original ← banks lhs
    let chosen ← banks paidLhs
    let paidTap ← view (← view paidLhs ``Sum.elim).getAppArgs.back! ``LedgerStep.substepWord
    let boundedDigit := mkFVar localArgs.back!
    let sameDigit ← mkEqRefl (Lean.Expr.proj ``Fin 0 boundedDigit)
    let terminalProof := mkAppN (← mkConstWithFreshMVarLevels ``postTap_same_memory_at_capped_digit)
      (args.extract 0 (args.size - 4) ++ original ++ #[chosen.back!,args[args.size - 2]!,args.back!,
        paidTap.getAppArgs.back!,sameDigit])
    main.assign terminalProof
    replaceMainGoal []


open Lean Elab Term Meta in
local elab "originalPositiveTap% " rankTerm:term " registeredBound " bounds:term " registeredPost " widths:term
    " onPaidReader " purchased:term " onTapWords " tapWord:term " onExternal " extTerm:term " onSelector " selTerm:term " onInnerBank " datTerm:term : term => do
  let rank ← withSynthesize (postpone := .no) <| elabTerm rankTerm none
  let high ← withSynthesize (postpone := .no) <| elabTerm bounds none
  let post ← withSynthesize (postpone := .no) <| elabTerm widths none
  let paid ← withSynthesize (postpone := .no) <| elabTerm purchased none
  let words ← withSynthesize (postpone := .no) <| elabTerm tapWord none
  let ext ← withSynthesize (postpone := .no) <| elabTerm extTerm none
  let sel ← withSynthesize (postpone := .no) <| elabTerm selTerm none
  let dat ← withSynthesize (postpone := .no) <| elabTerm datTerm none
  let .letE _ _ _ paidFamily _ := (← inferType paid).consumeMData | throwError "expected physical partition"
  let rec walk (fuel : Nat) (t : Lean.Expr) (right : Option Lean.Expr) (locals : Array Lean.Expr) : TermElabM Lean.Expr := do
    let fuel+1 := fuel | throwError "ranked read exceeds original telescope"
    match t.consumeMData with
    | .letE n _ value tail _ => do
      if n == `partsAt then
        let some parts := right | throwError "missing right partition"
        let .lam _ _ body _ := value.consumeMData | throwError "expected two-sided partition"
        let registered := body.instantiate1 (mkConst ``Bool.true)
        let .const fn _ := registered.getAppFn | throwError "missing partition's bool recursor"
        unless fn == ``Bool.rec && registered.getAppArgs[2]! == parts do throwError "true recursor branch changed"
        walk fuel (tail.instantiate1 value) right locals
      else walk fuel (tail.instantiate1 value) (if n == `rightParts then some value else right) locals
    | .forallE n dom tail _ => do
      if [`_reads,`reads].contains n then
        let some parts := right | throwError "missing carried post partition"
        let .forallE _ _ afterSide _ := dom.consumeMData | throwError "missing boolean side"
        let original := afterSide.instantiate1 (mkConst ``Bool.true)
        let purchasedAtRight := paidFamily.instantiate1 parts
        forallBoundedTelescope original (some 4) fun args result => do
          unless args.size==4 do throwError "unexpected source reader arity"
          let some (_,lhs,_) := (← whnf result).eq? | throwError "missing ranked equation"
          let mut p := purchasedAtRight
          for a in args do
            let .forallE _ _ b _ ← whnf p | throwError "expected physical reader operand"
            p := b.instantiate1 a
          let some (_,physical,_) := (← whnf p).eq? | throwError "missing paid equation"
          let eqn ← mkEq lhs physical
          let out ← mkForallFVars args eqn
          mkForallFVars locals out (usedOnly := true)
      else
        let choice := match n with
        | `high => some high | `postEq => some post | `words => some words | `ext => some ext
        | `sel => some sel | `data => some dat | _ => none
        if let some v := choice then walk fuel (tail.instantiate1 v) right locals
        else withLocalDeclD n dom fun arg => walk fuel (tail.instantiate1 arg) right (locals.push arg)
    | _ => throwError "original ranked read not found"
  return ShareCommon.shareCommon' (← walk 48 (← inferType rank) none #[])


open Lean Elab Term Meta in
local elab "signedOriginalPositive% " rankTerm:term " registeredBound " bounds:term " registeredPost " widths:term
    " originalEndpoint " endpoint:term " onTapWords " tapWord:term " onExternal " extTerm:term " onSelector " selTerm:term " onInnerBank " datTerm:term : term => do
  let rank ← withSynthesize (postpone := .no) <| elabTerm rankTerm none
  let high ← withSynthesize (postpone := .no) <| elabTerm bounds none
  let post ← withSynthesize (postpone := .no) <| elabTerm widths none
  let state ← withSynthesize (postpone := .no) <| elabTerm endpoint none
  let words ← withSynthesize (postpone := .no) <| elabTerm tapWord none
  let ext ← withSynthesize (postpone := .no) <| elabTerm extTerm none
  let sel ← withSynthesize (postpone := .no) <| elabTerm selTerm none
  let dat ← withSynthesize (postpone := .no) <| elabTerm datTerm none
  let rec walk (fuel : Nat) (t : Lean.Expr) (right : Option Lean.Expr) (locals : Array Lean.Expr) : TermElabM Lean.Expr := do
    let fuel+1 := fuel | throwError "ranked read exceeds original telescope"
    match t.consumeMData with
    | .letE n _ value tail _ => do
      if n == `partsAt then
        let some parts := right | throwError "missing right partition"
        let .lam _ _ body _ := value.consumeMData | throwError "expected two-sided partition"
        let registered := body.instantiate1 (mkConst ``Bool.true)
        let .const fn _ := registered.getAppFn | throwError "missing partition's bool recursor"
        unless fn == ``Bool.rec && registered.getAppArgs[2]! == parts do throwError "true recursor branch changed"
        walk fuel (tail.instantiate1 value) right locals
      else walk fuel (tail.instantiate1 value) (if n == `rightParts then some value else right) locals
    | .forallE n dom tail _ => do
      if [`_reads,`reads].contains n then
        let some _ := right | throwError "missing carried post partition"
        let .forallE _ _ afterSide _ := dom.consumeMData | throwError "missing boolean side"
        let original := afterSide.instantiate1 (mkConst ``Bool.true)
        forallBoundedTelescope original (some 4) fun args result => do
          unless args.size == 4 do throwError "original positive read is not four binders"
          let some (_, lhs, rhs) := (← whnf result).eq? | throwError "native ranked read lacks equation"
          unless lhs.getAppFn.isConstOf ``Sum.elim && rhs.getAppFn.isConstOf ``Nat.testBit do
            throwError "the ranked proposition changed"
          let out ← mkForallFVars args result
          mkForallFVars locals out (usedOnly := true)
      else
        let choice := match n with
        | `values => some state | `high => some high | `postEq => some post | `words => some words | `ext => some ext
        | `sel => some sel | `data => some dat | _ => none
        if let some v := choice then walk fuel (tail.instantiate1 v) right locals
        else withLocalDeclD n dom fun arg => walk fuel (tail.instantiate1 arg) right (locals.push arg)
    | _ => throwError "original ranked read not found"
  return ShareCommon.shareCommon' (← walk 48 (← inferType rank) none #[])

open Lean Elab Tactic Meta in
local elab "joinOriginalPostRead " lhsTerm:term:max " withPaidOutput " rhsTerm:term:max : tactic => do
  let (inputs, g) ← (← getMainGoal).intros
  unless inputs.size == 6 do throwError "expected original low, preEq, column, neighbor, owner, digit; found {inputs.size}"
  replaceMainGoal [g]
  withMainContext do
    let args := inputs.map mkFVar
    let names ← inputs.mapM fun f => return (← f.getDecl).userName.eraseMacroScopes
    unless names[0]! == `low && names[1]! == `preEq do throwError "pre-side names differ: {names}"
    let l := mkAppN (← Term.elabTermAndSynthesize lhsTerm none) args
    let r := mkAppN (← Term.elabTermAndSynthesize rhsTerm none) (args.extract 2 6)
    let some (boolTy, lhs, middle) := (← whnf (← inferType l)).eq? | throwError "registered taps were not equal"
    let some (_, _, out) := (← whnf (← g.getType)).eq? | throwError "expected ranked post goal"
    unless boolTy.isConstOf ``Bool do throwError "expected purchased bits"
    let both := mkAppN (mkConst ``Eq.trans [.succ .zero]) #[boolTy,lhs,middle,out,l,r]
    g.assign both
    replaceMainGoal []

-- Both incoming words are the selected physical state, cast to its paid width.
private theorem samePurchasedIncomingState {SourceA SourceB Result : Sort _}
    (toResultA : SourceA = Result) (toResultB : SourceB = Result)
    (a : SourceA) (b : SourceB) (same : HEq a b) : cast toResultA a = cast toResultB b :=
  eq_of_heq ((cast_heq toResultA a).trans (same.trans (cast_heq toResultB b).symm))

open Lean Meta in
private def moveReadToPurchasedState
    (openRead carrying rawEndpoint paid : Lean.Expr) : MetaM Lean.Expr := do
  let body := openRead.beta #[carrying]
  let .letE _ stateType observedState remaining _ := body.consumeMData
    | throwError "expected the transferred state in the purchased offer"
  let some observed ← whnfUntil observedState ``cast
    | throwError "expected the funded offer's cast from the chronological state"
  let some ranked ← whnfUntil rawEndpoint ``cast
    | throwError "expected the registered incoming endpoint's cast"
  let #[fromA,toState,pathA,stateA] := observed.getAppArgs | throwError "unexpected funded state cast"
  let #[fromB,_,pathB,stateB] := ranked.getAppArgs | throwError "unexpected ranked state cast"
  let eqState := mkAppN (Lean.mkConst ``samePurchasedIncomingState observed.getAppFn.constLevels!)
    #[fromA,fromB,toState,pathA,pathB,stateA,stateB,← mkHEqRefl stateA]
  let family := Lean.Expr.lam `incomingState stateType remaining .default
  -- Bind the right endpoint to the caller's dependent state verbatim.
  let changed := mkAppN (Lean.mkConst ``congrArg [← getLevel stateType, .succ .zero])
    #[stateType, mkSort .zero, observedState, rawEndpoint, family, eqState]
  return ← mkEqMP changed paid

open Lean Meta Elab Term in
local elab "postReadsAtPartsState% " evidence:term:max " usingPartsEq " agreement:term:max " atState " endpointTerm:term:max : term => do
  let physicalProof ← withSynthesize (postpone := .no) <| elabTerm evidence none
  let physicalType := (← inferType physicalProof).consumeMData
  let .letE chartBinder chartType _ chartBody _ := physicalType
    | throwErrorAt evidence "expected the initial carried-partition let of the purchased post read"
  let physicalFamily := Lean.Expr.lam chartBinder chartType chartBody .default
  let agreementProof ← instantiateMVars (← elabTerm agreement none)
  let agreementType ← whnf (← inferType agreementProof)
  let some (chartCarrier, firstChart, secondChart) := agreementType.eq?
    | throwErrorAt agreement "expected purchased partition = registered partition"
  let universeOfCharts := agreementType.getAppFn.constLevels!.head!
  let proofOfTransport := mkAppN (mkConst ``congrArg [universeOfCharts, .succ .zero])
    #[chartCarrier, mkSort .zero, firstChart, secondChart, physicalFamily, agreementProof]
  let onPartition := mkAppN (mkConst ``Eq.mp [.zero])
    #[mkApp physicalFamily firstChart, mkApp physicalFamily secondChart, proofOfTransport, physicalProof]
  let rawEndpoint ← withSynthesize (postpone := .no) <| elabTerm endpointTerm none
  moveReadToPurchasedState physicalFamily secondChart rawEndpoint onPartition

open Lean Meta Elab Tactic in
local elab "transferPurchasedIncoming " offer:term:max " across " rowCode:term:max
    " tables " columns:term:max " registers " rawTable:term:max " keys " physicalKey:term:max
    " attempt " isAttempt:term:max " widths " physicalWidths:term:max
    " atIncomingState " endpointTerm:term:max : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let offerProof ← Term.elabTermAndSynthesize offer none
    let target ← goal.getType
    let rankedParts ← forallBoundedTelescope target (some 2) fun laneAndOwner tail => do
      unless laneAndOwner.size == 2 do throwError "expected the ranked slot and its recorded owner"
      let .forallE _ occupied _ _ := (← whnf tail) | throwError "expected ranked slot occupancy"
      let some (_,lhs,_) := occupied.consumeMData.eq? | throwError "expected the original owner equation"
      let projection := lhs.consumeMData.appFn!.consumeMData
      let parts ← match projection with
        | .proj struct idx value => do
          let some field := (← getEnv).getProjectionFnInfo? ``PassiveWindow.Parts.owner | throwError "missing partition owner"
          unless struct == ``PassiveWindow.Parts && field.i == idx do throwError "unexpected ranked projection"
          pure value
        | _ => do
          unless projection.getAppFn.isConstOf ``PassiveWindow.Parts.owner do throwError "expected the ranked partition's owner field, found {projection.getAppFn.constName?}"
          pure projection.appArg!
      let some original ← whnfUntil parts ``PassiveWindow.carried | throwError "the false branch does not select the registered incoming partition"
      return original
    let mut form ← inferType offerProof
    let mut replacements := #[]
    for _ in [:24] do
      match form with
      | .letE nm _ rhs body _ =>
        if nm == `carrying then break
        replacements := replacements.push (rhs.instantiateRev replacements)
        form := body
      | .mdata _ body => form := body
      | _ => break
    let .letE `carrying domain value body _ := form | throwError "the purchased offer has no recorded carrying partition"
    let offeredParts := value.instantiateRev replacements
    let readAt := (Lean.Expr.lam `carrying domain body .default).instantiateRev replacements
    let operands ← #[rowCode, columns, rawTable, physicalKey, isAttempt, physicalWidths].mapM fun term =>
      Term.elabTermAndSynthesize term none
    let agreement ← FundedDate.makePaidApertureEquality offeredParts rankedParts
      operands[0]! operands[1]! operands[2]! operands[3]! operands[4]! operands[5]!
    let result ← mkEqMP (← mkCongrArg readAt agreement) offerProof
    let incoming ← Term.elabTermAndSynthesize endpointTerm none
    goal.assign (← moveReadToPurchasedState readAt rankedParts incoming result)
    replaceMainGoal []

open private calendarOriginalMeasurements calendarPhysicalMeasurementResult preclipSiteFormula from
  OAI.Hierarchy.TaggedWideCalendarAttemptAt

private theorem paidSettlementChart_eq {K N : Nat} {bits : Fin K → Type}
    {chart : Sigma bits ↪ (Fin K × Fin N)} (paid : preclipSiteFormula (Fin K) bits (Fin N) chart) :
    @paidReadSiteChart K N bits chart paid = @LedgerStep.siteChart K N bits chart paid := rfl

open Lean Elab Term Meta in
local elab "settlementWithChartFamily%" : term => do
  let original ← getConstInfo ``calendarOriginalMeasurements
  forallTelescope original.type fun args _ => do
    let .forallE `run _ tail _ := (original.value!.beta args).consumeMData
      | throwError "expected the signed original row premise"
    let .forallE `settle domain _ _ := tail.consumeMData
      | throwError "expected the second original row premise"
    if domain.hasLooseBVars then throwError "the settlement premise depends on the signed proof"
    let isChart := fun (e : Lean.Expr) => e.isAppOfArity ``LedgerStep.siteChart 5
    let some usedChart := Lean.Expr.find? isChart domain | throwError "the original settle premise has no site chart"
    if usedChart.hasLooseBVars then throwError "the chart itself depends on an exit or intermediate state"
    withLocalDeclD `physicalChart (← inferType usedChart) fun chartArg => do
      let replaced := Lean.Expr.replace (fun e =>
        if isChart e && e == usedChart then some chartArg else none) domain
      if (Lean.Expr.find? isChart replaced).isSome then throwError "the original row used distinct site charts"
      let tailNames ← (args.extract (args.size-2) args.size).mapM fun arg => return (← arg.fvarId!.getDecl).userName
      unless tailNames == #[`layout,`site] do throwError "expected the original layout and site proof"
      let result ← mkLambdaFVars ((args.extract 0 (args.size-2)).push chartArg) replaced
      if result.hasFVar then throwError "the charted settlement retained an independent layout or site reference"
      return result

private def originalSettlementWithChart := settlementWithChartFamily%

open Lean Elab Term Meta in
local elab "physicalSettlementOnPaidChart%" : term => do
  let sheet ← getConstInfo ``calendarPhysicalMeasurementResult
  forallTelescope sheet.type fun args _ => do
    let old := (sheet.value!.beta args).consumeMData
    unless old.isAppOf ``calendarOriginalMeasurements do throwError "expected the folded row result"
    let paid := args.back!
    unless (← paid.fvarId!.getDecl).userName == `placementSite do throwError "expected the retained site proof"
    let law := (← inferType paid).consumeMData
    unless law.isAppOfArity ``preclipSiteFormula 4 do throwError "expected the retained four-argument site law"
    let #[sites,bits,lanes,placement] := law.getAppArgs | throwError "expected physical chart operands"
    let some siteFin ← whnfUntil sites ``Fin | throwError "expected a finite site"
    let some laneFin ← whnfUntil lanes ``Fin | throwError "expected a finite lane"
    let chart := mkAppN (← mkConstWithFreshMVarLevels ``paidReadSiteChart)
      #[siteFin.appArg!,laneFin.appArg!,bits,placement,paid]
    let pred ← mkConstWithFreshMVarLevels ``originalSettlementWithChart
    let rowArgs := old.getAppArgs
    mkLambdaFVars args (mkApp (mkAppN pred (rowArgs.extract 0 (rowArgs.size-2))) chart)

private def physicalSettlementOnPaidChart := physicalSettlementOnPaidChart%

-- Use this term directly as the type of wide_calendar_spill_at. A separate
-- Prop-valued public definition would recompile the complete purchased path.
open Lean Elab Term Meta in
local elab "paidSpillSettlement% " "[" values:term,* "]" : term => do
  let format ← getFVarFromUserName `v
  let some fty ← whnfUntil (← inferType format) ``FixedProtocolFormat | throwError "expected the fixed protocol format"
  let mut args := fty.getAppArgs
  for v in values.getElems do args := args.push (← elabTerm v none)
  let info ← getConstInfo ``calendarAttemptMeasurements
  let mut tail := info.type
  for _ in [:args.size] do
    let .forallE _ _ body _ := tail | throwError "too many original measurement arguments"
    tail := body
  unless tail.isAppOf ``calendarPhysicalMeasurementResult do throwError "expected all original measurement arguments"
  let actual := tail.instantiateBetaRevRange 0 args.size args
  return mkAppN (← mkConstWithFreshMVarLevels ``physicalSettlementOnPaidChart) actual.getAppArgs

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
local notation "unit" => v.calendarUnit
variable (cpu : v.ParentFullCPUs m ell short u δ ξ v.calendarUnit N x) (room : cpu.SiteRoom)
    (control : SignedSites.CalendarControlRoom (cpu:=cpu))
    (support : v.SelectedReturnSupport m ell short u δ ξ v.calendarUnit v.calendarUnit_rate x)
local notation "h" => x.h
local notation "width" => x.w
local notation "d" => 2^v.W
local notation "g" => v.wideDated h width ell unit
local notation "S" => v.wideInstalledSize x m ell unit g
local notation "Sfit" => (v.wide_installed_tape_bounds x m ell unit g).2.2
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unit g
    (v.wide_dated_sites h width ell unit) (v.wide_dated_edges h width ell unit) (fun _=>0)
local notation "reader" => v.wideSelector h width cpu.age cpu.ready.credit cpu.ready.size_le
local notation "sl" => (reader).format.slot
local notation "es" => events v.mesh
local notation "D" => v.parentShared x m ell short unit ((es).length+1)
local notation "menu" => (typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ
local notation "slots" => purchaseSlots h v.W k v.wideJobs ell
local notation "base" => v.wideOrigin h width S seed

variable (routeAge : v.routingHeight≤x.h)
local notation "arenaRoom" => (v.wide_funded_extent h width v.maxBits).trans Sfit
local notation "Z" => v.routedSchedule h width S arenaRoom seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit routeAge support.size.widthFloor support.size.words
local notation "rout" => (Z).nativeRouting D
local notation "sites" => SignedSites.ofCalendar (cpu:=cpu) Z control v.calendarTerminalWidth
  (v.calendarTerminalPins x m ell short)
local notation "source" => fun _ : Fin (m+1)=>slots
local notation "count" => purchaseModules v.W u δ ξ menu x
local notation "target" => fun i=>purchaseCandidates h v.W k v.wideJobs slots ((menu).height i x) (count i)
local notation "Buy" => PurchaseList (F:=F) (C:=C) menu x source target count
local notation "Ex" => OpenPins h width (rout).catalyst
local notation "report" π:arg j:arg => v.wide_reported_path h width S π seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit support.size.late support.size.words j
variable (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
variable (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
local notation "path" => (Fintype.equivFin (Path sl es (base perm))).symm i
local notation "record" => CalendarTape.encode sl es (base perm) path

open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.BranchRoles Tagged.WideCalendarSites
open ThreeFlat Routing
open LinearAlgebra.SpectralBooks ChordGraph
open Tagged.WideStack.Leaf ProtocolRAMReportedPorts
variable (height : v.BranchRoleHeight h width)
local notation "G" => (v.wideFullGates x m ell short u δ ξ unit cpu.room).2
local notation "W" => Native.wordBits h d Native.copies
local notation "root" => (WireTelescope.CalendarTape.Prefix.start : WireTelescope.CalendarTape.Prefix sl es (base perm) es (base perm))
local notation "tree" => WireTelescope.CalendarTape.Prefix.cursorSlot («slot»:=sl) (events:=es) (x₀:=base perm)
local notation "ws" => WireTelescope.CalendarTape.Prefix.atWidth ((Z).width perm)
local notation "top" => WireTelescope.CalendarTape.Prefix.atCursor root
local notation "branch" => WireTelescope.CalendarTape.Prefix.histories root path
local notation "stop" => terminal tree es top branch
local notation "input" => (reader).format.windows.header es record seed
local notation "bill" => v.wide_reported_path_native h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit support.size.late support.size.words path
local notation "admitted" => (bill).choose
local notation "cost" => (bill).choose_spec.choose
local notation "names" => (bill).choose_spec.choose_spec.choose
local notation "accepted" => (bill).choose_spec.choose_spec.choose_spec.1
local notation "native" => v.wide_native_report h width S perm.symm input v.maxBits Sfit admitted
  cpu.ready.credit cpu.ready.size_le cost (0:Word W) names
local notation "runAt" => v.wide_selected_local_return m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path
local notation "out" => (runAt).2.2.2.choose
local notation "actual" => Classical.choice (support.funding S Sfit perm.symm input admitted cpu.ready.credit
  cpu.ready.size_le cost (0:Word W) names accepted)
local notation "install" ok:arg => FundedCutRows.rowData v x S perm.symm input m ell short unit (native).rows
  (native).geometry actual prices pricePos buy groupsFit metadata ok lanesFit
local notation "geom" => typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)
local notation "dir" => WideMemory.dir h v.W k v.wideJobs
local notation "ports" => WideMemory.H h v.W k v.wideJobs
local notation "b" => (v.widePlacement h width).catalogue
local notation "order" => v.wideOrder h width
local notation "roles" => HistoryRoles.ceiling v.sampler («h»:=h) («W»:=v.W) (k:=k) (attempts:=v.wideJobs)
  v.mesh unit v.keepLimit (fuel v.mesh) width
local notation "view" => v.wideHistoryUnit unit*width
local notation "times" => ((es).length+1)*Fintype.card ((r:Public v.sampler h v.W k v.wideJobs)×Fin (roles r))
local notation "shape" => v.widePathRoles h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le Sfit
  height.report height.wordRoom path unit height.replay height.measure (height.funded_aperture S unit Sfit v.calendarUnit_rate)
local notation "pins" => v.widePathCells h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le Sfit
  height.report height.wordRoom path unit height.replay height.measure (height.funded_aperture S unit Sfit v.calendarUnit_rate)
local notation "place" => timelineFin tree ws pins es top branch
local notation "replayed" => cursorReport perm ((Z).width perm) ((Z).reported perm) branch
local notation "Rpt" => CoreBoard.Report perm d k width (fuel v.mesh*width) v.radius 1 (ws stop)
local notation "table" r:arg => (⟨(r).edges,(r).rows⟩ : CalendarTerms.RowBoard)
local notation "plan" r:arg => CalendarTerms.RankedRows (F:=F) (geom).index D (dir).groups ports (2^ell) width m times view (table r)

local notation "same" => v.wide_selected_geometry m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path
local notation "sameRows" => congrArg (fun r:RowGeometry h d k width (fuel v.mesh*width) v.radius 1=>
  (⟨r.1,r.2.1⟩:CalendarTerms.RowBoard)) same
local notation "kept" => (native).geometry.links.Keep (2^h)
local notation "recorded" => v.wideCalendarPartyPlace m ell short u δ ξ x cpu Z perm i height (fun _=>rfl)
local notation "rnk" ok:arg => CalendarTerms.RankedRows.onBranch Z perm i sameRows (install ok)
local notation "wordTable" => (r : Fin (replayed).edges)→Fin (2^((replayed).rows r).width)
local notation "states" => SiteChoices tree ws es top branch

local notation "data" ok:arg words:arg q:arg => v.calendarDayPins (C:=C) m ell short u δ ξ x cpu support routeAge
  prices pricePos groupsFit metadata lanesFit buy e perm i tag height ok words q
local notation "scr" => v.wideInstalledLayout x m ell short u δ ξ unit g
local notation "first" => (scr).pruneScratch+(scr).pruneRows+1
local notation "rom" => v.wideInstalledRoot x
local notation "time" => SignedSites.calendarTime (v:=v) (x:=x) (m:=m) (ell:=ell) (short:=short) (unitCost:=unit)
local notation "actualRow" s:arg j:arg => v.calendarRow h width ell unit v.maxBits rom S ((g).romEnd rom) ((g).workEnd S)
  first G time s j (control.spillRead s j) (control.signedRead s j) (control.mode s j) control.tag control.lane
local notation "step" => WireTelescope.CalendarTape.Prefix.atStep ((Z).width perm) ((Z).operator perm)
local notation "matrixAt" j:arg => indexedStep tree ws step es top branch j
local notation "valAt" q:arg s:arg j:arg => datedState tree ws s es top branch j (q s)


-- Use the stored physical operand type from the selected calendar day's own interface.
open Lean Elab Term in
local elab "calendarFundedOperand% " selected:str : term => do
  let original ← getConstInfo ``calendarDayPins
  let selection := Name.mkSimple selected.getString
  let format := (← Meta.inferType (← Meta.getFVarFromUserName `v)).getAppArgs
  let field := format[1]!
  let ambientRatio := format[4]!
  let mut current := original.type
  let mut supplied : Array Lean.Expr := #[]
  for _ in [:100] do
    match current with
    | .forallE binder domain rest info =>
      if binder == selection then return domain.instantiateRev supplied
      let argument ← if info == .instImplicit then pure field else if binder == `q then pure ambientRatio else Meta.getFVarFromUserName binder
      supplied := supplied.push argument
      current := rest
    | _ => break
  throwError "the original funded day has no physical operand {selection}"

variable (date : Fin (es).length) (a : Attempt) (day : (es).get date=.attempt a)
    (ok : calendarFundedOperand% "ok") (words : calendarFundedOperand% "words")
    (q : calendarFundedOperand% "statesAt") (site : Fin (siteLast h d k+1))
local notation "voteAt" => v.wide_routed_attempt_on_visit h width S arenaRoom perm seed cpu.age cpu.ready.credit
  cpu.ready.size_le Sfit routeAge support.size.widthFloor support.size.words path date day
local notation "x₀" => valAt q site date.castSucc
local notation "y₀" => valAt q site date.succ

local notation "siteLaw" => applyCalendarLayoutOperand% selectedPreclipSiteOnNamedLayout [κ, A, v, m, ell, short, u, δ, ξ, unit, N, x, cpu, v.calendarUnit_rate, support, prices, C, pricePos, buy, groupsFit, metadata, lanesFit, (rout).catalyst, e, perm, tag, path, routeAge, height, date, a, day]
open LinearAlgebra.SpectralBooks.SiteTensor
open WideCPU WideControlJoin
local notation "visit" => Prefix.pathVisitAt path date day
local notation "stamp" => (es).length-(Event.attempt a::(visit).tail).length
local notation "whereAt" => siteNumber h d k
local notation "nativeSlots" => v.nativeSlots (v.widePlacement h width) h width a
local notation "cut" c:arg => v.wide_funded_date h width S arenaRoom perm seed cpu.age cpu.ready.credit
    cpu.ready.size_le (visit).prior c
local notation "ref" => v.wide_reference_date h width S arenaRoom perm seed cpu.age cpu.ready.credit
    cpu.ready.size_le (visit).prior
local notation "oldMount" => (b).coreMount perm.symm whereAt order (visit).mem
local notation "spent" => v.wirePaidAt h width v.maxBits stamp (visit).mem
local notation "avail" => fun ledgerGood=>v.wireGoodsAt h width stamp (visit).mem ((nativeSlots).symm ledgerGood)
local notation "reserve" c:arg => fun axis=>(fuel v.mesh*width-v.wireUsedAt h width stamp (visit).mem axis)-
    (cut c).reserveDebit axis
local notation "rest" => (oldMount).actual.chordWidths spent +
    (CoreBoard.ordinalGoods perm.symm whereAt nativeSlots).chordWidths (fun ledgerGood=>(avail) ledgerGood-(cut (ref).1).debit ledgerGood) +
    (catalystGraph whereAt).chordWidths (reserve (ref).1)
local notation "pos" => (visit).choice
local notation "slotsUsed" => fun l=>((ref).2.row arenaRoom support.size.tenderAge support.size.widthFloor l).input
local notation "offered" => fun l=>((ref).2.tender arenaRoom support.size.tenderAge support.size.widthFloor l).post (pos l)
local notation "U" => rest+∑l,slotsUsed l
local notation "V" => rest+∑l,offered l
local notation "carry" => (oldMount).actual.chordWidths spent+(cut pos).afterMount.actual.chordWidths (cut pos).paid+
    (catalystGraph whereAt).chordWidths (reserve pos)
local notation "transfer" => FeedTransfer.afterVote nativeSlots (fun c=>(cut c).afterGoods) (fun c=>(cut c).spill) pos
local notation "middleWidth" => FeedTransfer.input (π:=perm.symm) («place»:=whereAt) carry transfer
local notation "beforeWidth" => ws (boundaryState tree es top branch date.castSucc)
local notation "whereNext" => ws (boundaryState tree es top branch date.succ)
local notation "sockets" => shelfSlot («h»:=h) («W»:=v.W) (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "taps" => LedgerStep.substepWord (cap:=v.wideNeighborCap width unit) G es roles sockets time date site true
local notation "inner" z:arg => LedgerStep.middle site (paidReadSiteChart% (siteLaw) atSite site) z
local notation "future" => v.wide_funded_date_with h width S arenaRoom perm seed cpu.age cpu.ready.credit
  cpu.ready.size_le (visit).prior (visit).choice (visit).future
local notation "owed" => carry+(commodityGraph perm.symm whereAt).chordWidths ((cut pos).afterGoods ∘ nativeSlots)
local notation "spillRegisters" => v.wide_selected_spill_registers m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path

-- Read the original named operand directly from the selected register's physical specification.
open Lean Elab Term in
local elab "registeredSpillOperand% " fieldName:ident " from " receipt:term : term => do
  let issued ← withSynthesize (postpone := .no) <| elabTerm receipt none
  let some issuedType ← Meta.whnfUntil (← Meta.inferType issued) ``NativeSpillRegisters.Evidence
    | throwErrorAt receipt "expected the selected physical spill register"
  let some spec ← Meta.unfoldDefinition? issuedType.appArg! (ignoreTransparency := true)
    | throwErrorAt receipt "expected the selected register's physical specification"
  let some typeName := spec.getAppFn.constName?
    | throwErrorAt receipt "expected a declared register specification"
  unless typeName.getString! == "nativeRegisterFieldTypes" do
    throwErrorAt receipt "expected the native spill-register field specification"
  let decl ← getConstInfo typeName
  let index ← Meta.forallTelescope decl.type fun xs _ => do
    let operandNames ← xs.mapM fun argument => return (← argument.fvarId!.getDecl).userName
    let some i := operandNames.idxOf? fieldName.getId.eraseMacroScopes
      | throwErrorAt fieldName "unknown physical spill-register operand"
    return i
  let some value := spec.getAppArgs[index]? | throwErrorAt fieldName "missing physical spill-register operand"
  return value

open Lean Elab Term in
local elab "registeredSpillCheckout% " evidence:term : term => do
  let issued ← withSynthesize (postpone := .no) <| elabTerm evidence none
  let some field := (← getEnv).getProjectionFnInfo? ``NativeSpillRegisters.Evidence.stored
    | throwErrorAt evidence "expected the native spill checkout field"
  return .proj ``NativeSpillRegisters.Evidence field.i issued

local notation "atPrune" => registeredSpillOperand% initial from spillRegisters
local notation "stock₀" => v.fixedTerminalStock (v.widePlacement h width) h width
local notation "topMem" => (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh
local notation "checkout" => v.wideSignedCheckoutAt h width S stock₀ v.radius perm.symm (wideRouteOrder h d k)
  (v.wideFundedRaw h width v.maxBits input)
local notation "checkedMount" => (b).coreMount perm.symm whereAt order checkout
local notation "spill" => fun z : Goods h v.W k=>RouteSettlement.actual
  (v.wideSpillPage h width v.maxBits first date.val).overflow atPrune (PurchaseInventory.slot z)
local notation "active₀" => (commodityGraph perm.symm whereAt).chordWidths spill
local notation "active₁" => (checkedMount).actual.chordWidths (routeLoad (checkedMount).ordinary spill)
local notation "correct" => v.wideSpillDates h width ell unit v.maxBits first
local notation "bound" => v.wideNeighborCap width unit
local notation "ends" => sorted v.sampler perm.symm v.depth (shape).mark ∘ (shape).order
local notation "outW" => FeedTransfer.output (cut pos).afterMount carry transfer

private theorem selectedRankedAttemptBound {n cap : ℕ} {inAttempt : Bool}
    {correctedAmounts uncorrectedAmounts : Fin n → ℕ} (isAttempt : inAttempt = true)
    (fits : ∀ r, correctedAmounts r ≤ cap) : ∀ r, (if inAttempt then correctedAmounts else uncorrectedAmounts) r ≤ cap := by
  subst inAttempt
  exact fits

private theorem selectedRankedAttemptShape {n siteCount : ℕ} {inAttempt : Bool}
    {rowEnds : Fin n → Chord siteCount} {correctedAmounts uncorrectedAmounts : Fin n → ℕ} {expectedWidth : Widths siteCount}
    (isAttempt : inAttempt = true) (measured : installedWidths rowEnds correctedAmounts = expectedWidth) :
    installedWidths rowEnds (if inAttempt then correctedAmounts else uncorrectedAmounts) = expectedWidth := by
  subst inAttempt
  exact measured

local notation "inputs" => v.selectedPreclipInputs m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path
local notation "sheetRows" => FundedDate.rankedPreclipPinsAt (v:=v) («h»:=h) («width»:=width)
  («size»:=S) (π:=perm) («seed»:=seed) («age»:=cpu.age) («budget»:=cpu.ready.credit) («small»:=cpu.ready.size_le)
  first inputs
local notation "tableAt" code:arg => FundedDate.selectedPreclipIssueTableAt (v:=v) («h»:=h) («width»:=width)
  («size»:=S) (π:=perm) («seed»:=seed) («age»:=cpu.age) («budget»:=cpu.ready.credit) («small»:=cpu.ready.size_le)
  code Sfit height.measure

section
variable (vertex : Site h d k)
local notation "numbered" => (whereAt) vertex
local notation "hiddenCount" => HistoryRoles.stride k v.sampler.degree v.wideJobs * bound

set_option maxHeartbeats 3500000 in
private theorem positivePurchasedPartitionMatchesRank
    {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) {N : ℕ} (x : WideParent κ A)
    (cpu : v.ParentFullCPUs m ell short u δ ξ v.calendarUnit N x) (support : v.SelectedReturnSupport m ell short u δ ξ v.calendarUnit v.calendarUnit_rate x)
    (routeAge : v.routingHeight≤x.h)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ) (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x) (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x) (lanesFit : v.wideInstalledCap unit≤2^ell)
    (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm)) (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
    (height : v.BranchRoleHeight h width)
    (date : Fin (es).length) (a : Attempt) (day : (es).get date=.attempt a)
    (ok : calendarFundedOperand% "ok") (words : calendarFundedOperand% "words")
    (q : calendarFundedOperand% "statesAt")
    (vertex : Site h d k)
    (observedWidth : installedWidths ends ((shape).bits date.succ) = owed+active₁)
    (hidden : Fin hiddenCount → Bool) :
    paidRankedPostPartitions% (v.wide_ranked_spill_carry («X»:=Ex) («Y»:=Fin (CalendarTape.bits sl es))
      («Z»:=D ⊕ Fin hiddenCount) m ell short u δ ξ unit x cpu v.calendarUnit_rate support prices pricePos
      buy groupsFit metadata lanesFit e perm tag path height date (G) rfl vertex owed)
    usingRankUpper (fun r => ((shape).fits date.succ r false).trans (v.wide_outer_lane h width unit
      ((named v.sampler perm.symm v.depth (shape).mark (shape).exclusive (shape).order) (r,false))))
    usingRankPostEq observedWidth
    usingRankPaidRead (v.calendar_day_spill_post_bits m ell short u δ ξ x cpu support routeAge prices pricePos groupsFit metadata
      lanesFit buy e perm i tag height ok words q date numbered (owed+active₁) observedWidth hidden)
:= positivePartitionRefl
end

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun xs => "positivePurchasedPartitionMatchesRank" :: xs

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun suggestionSuffixes => "recordedPreclipPins" :: suggestionSuffixes

private theorem recordedPreclipPins
    {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) {N : ℕ} (x : WideParent κ A)
    (cpu : v.ParentFullCPUs m ell short u δ ξ v.calendarUnit N x) (support : v.SelectedReturnSupport m ell short u δ ξ v.calendarUnit v.calendarUnit_rate x)
    (routeAge : v.routingHeight≤x.h)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ) (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x) (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x) (lanesFit : v.wideInstalledCap unit≤2^ell)
    (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm)) (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
    (height : v.BranchRoleHeight h width)
    (date : Fin (es).length) (a : Attempt) (day : (es).get date=.attempt a) :
    sheetRows record date (registeredSpillOperand% issues from spillRegisters) bound (owed+active₀) := by
  have key:=v.selectedPreclipCode m ell short u δ ξ unit x cpu perm path date a day
  have before:=v.selected_spill_input_width m ell short u δ ξ unit x cpu v.calendarUnit_rate support
    prices pricePos buy groupsFit metadata lanesFit e perm tag path routeAge height date a day
  have origin:=v.wide_selected_preclip_strict m ell short u δ ξ unit x cpu v.calendarUnit_rate support
    prices pricePos buy groupsFit metadata lanesFit e perm tag path height date a day
  apply FundedDate.transferPrintedPins
    (fun encoded calendarDay issuedTable => sheetRows encoded calendarDay issuedTable bound (owed+active₀))
    (fun code => tableAt code) key.1 key.2 (Eq.refl (registeredSpillOperand% issues from spillRegisters))
  exact ⟨fun r => (origin.1 r false).trans (v.selectedPreclipWithin unit x), before⟩

local notation "settledAtSite" numberedSite:arg => paidSpillSettlement% [κ,A,C,v,m,ell,short,u,δ,ξ,N,x,cpu,control,support,
    routeAge,prices,pricePos,groupsFit,metadata,lanesFit,buy,e,perm,i,tag,height,date,a,day,ok,words,q,numberedSite]

set_option maxHeartbeats 6500000 in
section
variable (vertex : Site h d k)
local notation "numbered" => (whereAt) vertex
local notation "hiddenCount" => HistoryRoles.stride k v.sampler.degree v.wideJobs * bound

set_option maxHeartbeats 3500000 in
private theorem originalPositiveTapValuations
    {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) {N : ℕ} (x : WideParent κ A)
    (cpu : v.ParentFullCPUs m ell short u δ ξ v.calendarUnit N x) (support : v.SelectedReturnSupport m ell short u δ ξ v.calendarUnit v.calendarUnit_rate x)
    (routeAge : v.routingHeight≤x.h)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ) (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x) (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x) (lanesFit : v.wideInstalledCap unit≤2^ell)
    (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm)) (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
    (height : v.BranchRoleHeight h width)
    (date : Fin (es).length) (a : Attempt) (day : (es).get date=.attempt a)
    (ok : calendarFundedOperand% "ok") (words : calendarFundedOperand% "words")
    (q : calendarFundedOperand% "statesAt")
    (vertex : Site h d k)
    (observedWidth : installedWidths ends ((shape).bits date.succ) = owed+active₁)
    (hidden : Fin hiddenCount → Bool) :
    originalPositiveTap% (v.wide_ranked_spill_carry («X»:=Ex) («Y»:=Fin (CalendarTape.bits sl es))
      («Z»:=D ⊕ Fin hiddenCount) m ell short u δ ξ unit x cpu v.calendarUnit_rate support prices pricePos
      buy groupsFit metadata lanesFit e perm tag path height date (G) rfl vertex owed)
    registeredBound (fun r => ((shape).fits date.succ r false).trans (v.wide_outer_lane h width unit
      ((named v.sampler perm.symm v.depth (shape).mark (shape).exclusive (shape).order) (r,false))))
    registeredPost observedWidth
    onPaidReader (v.calendar_day_spill_post_bits m ell short u δ ξ x cpu support routeAge prices pricePos groupsFit metadata
      lanesFit buy e perm i tag height ok words q date numbered (owed+active₁) observedWidth hidden)
    onTapWords (LedgerStep.substepWord («Ex»:=Ex) («Sel»:=Fin (CalendarTape.bits sl es)) (cap:=v.wideNeighborCap width unit) G es roles sockets time date numbered true)
    onExternal e onSelector record onInnerBank (Sum.elim (data ok words q) hidden) := by
  compareOriginalPositiveTaps

set_option hygiene false in
local notation "rankedChartRead" =>
  let joinedParts := applyCalendarLayoutOperand% positivePurchasedPartitionMatchesRank
    [κ, A, C, v, m, ell, short, u, δ, ξ, N, x, cpu, support, routeAge, prices, pricePos,
      groupsFit, metadata, lanesFit, buy, e, perm, i, tag, height, date, a, day, ok, words, q, vertex, observedWidth, hidden]
  let right := cast (congrArg (fun T=>State T numbered) (((shape).atWidth date.succ).symm.trans observedWidth))
    (valAt q numbered date.succ)
  postReadsAtPartsState% (v.calendar_day_spill_post_bits m ell short u δ ξ x cpu support routeAge prices pricePos groupsFit metadata
    lanesFit buy e perm i tag height ok words q date numbered (owed+active₁) observedWidth hidden) usingPartsEq joinedParts atState right

private theorem physicalPostReadWithRankedChartState
    {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) {N : ℕ} (x : WideParent κ A)
    (cpu : v.ParentFullCPUs m ell short u δ ξ v.calendarUnit N x) (support : v.SelectedReturnSupport m ell short u δ ξ v.calendarUnit v.calendarUnit_rate x)
    (routeAge : v.routingHeight≤x.h)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ) (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x) (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x) (lanesFit : v.wideInstalledCap unit≤2^ell)
    (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm)) (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
    (height : v.BranchRoleHeight h width)
    (date : Fin (es).length) (a : Attempt) (day : (es).get date=.attempt a)
    (ok : calendarFundedOperand% "ok") (words : calendarFundedOperand% "words")
    (q : calendarFundedOperand% "statesAt")
    (vertex : Site h d k)
    (observedWidth : installedWidths ends ((shape).bits date.succ) = owed+active₁)
    (hidden : Fin hiddenCount → Bool) :
    type_of% rankedChartRead := rankedChartRead

set_option maxHeartbeats 3500000 in
private theorem completeOriginalRankedPositiveRead
    {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) {N : ℕ} (x : WideParent κ A)
    (cpu : v.ParentFullCPUs m ell short u δ ξ v.calendarUnit N x) (support : v.SelectedReturnSupport m ell short u δ ξ v.calendarUnit v.calendarUnit_rate x)
    (routeAge : v.routingHeight≤x.h)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ) (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x) (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x) (lanesFit : v.wideInstalledCap unit≤2^ell)
    (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm)) (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
    (height : v.BranchRoleHeight h width)
    (date : Fin (es).length) (a : Attempt) (day : (es).get date=.attempt a)
    (ok : calendarFundedOperand% "ok") (words : calendarFundedOperand% "words")
    (q : calendarFundedOperand% "statesAt")
    (vertex : Site h d k)
    (observedWidth : installedWidths ends ((shape).bits date.succ) = owed+active₁)
    (hidden : Fin hiddenCount → Bool)
    (actualPre : State (owed+active₀) numbered) :
    signedOriginalPositive% (v.wide_ranked_spill_carry («X»:=Ex) («Y»:=Fin (CalendarTape.bits sl es))
      («Z»:=D ⊕ Fin hiddenCount) m ell short u δ ξ unit x cpu v.calendarUnit_rate support prices pricePos
      buy groupsFit metadata lanesFit e perm tag path height date (G) rfl vertex owed)
    registeredBound (fun r => ((shape).fits date.succ r false).trans (v.wide_outer_lane h width unit
      ((named v.sampler perm.symm v.depth (shape).mark (shape).exclusive (shape).order) (r,false))))
    registeredPost observedWidth
    originalEndpoint (Bool.rec (motive:=fun side=>State (owed+cond side active₁ active₀) numbered)
      actualPre (cast (congrArg (fun T=>State T numbered) (((shape).atWidth date.succ).symm.trans observedWidth))
        (valAt q numbered date.succ)))
    onTapWords (LedgerStep.substepWord («Ex»:=Ex) («Sel»:=Fin (CalendarTape.bits sl es)) (cap:=v.wideNeighborCap width unit) G es roles sockets time date numbered true)
    onExternal e onSelector record onInnerBank (Sum.elim (data ok words q) hidden) := by
  joinOriginalPostRead (applyCalendarLayoutOperand% originalPositiveTapValuations [κ, A, C, v, m, ell, short, u, δ, ξ, N, x, cpu, support, routeAge, prices, pricePos, groupsFit, metadata, lanesFit, buy, e, perm, i, tag, height, date, a, day, ok, words, q, vertex, observedWidth, hidden])
    withPaidOutput (applyCalendarLayoutOperand% physicalPostReadWithRankedChartState [κ, A, C, v, m, ell, short, u, δ, ξ, N, x, cpu, support, routeAge, prices, pricePos, groupsFit, metadata, lanesFit, buy, e, perm, i, tag, height, date, a, day, ok, words, q, vertex, observedWidth, hidden])

end

open Lean Elab Tactic Meta in
local elab "closePurchasedPositive " certified:term : tactic => withMainContext do
  let main ← getMainGoal
  let reading ← instantiateMVars (← Term.elabTermAndSynthesize certified none)
  unless reading.getAppFn.constName?.any (fun n => n.getString! == "completeOriginalRankedPositiveRead") &&
      reading.getAppNumArgs == 46 && !reading.hasMVar do
    throwError "expected the complete purchased positive reader on all 46 operands"
  main.assign reading
  replaceMainGoal []

private theorem useCertifiedPostWidth (widthClaim consequence : Prop)
    (withWidth : widthClaim → consequence) (purchasedWidth : widthClaim) : consequence :=
  withWidth purchasedWidth

open Lean Elab Tactic Meta in
local elab "underCertifiedPostWidth " witness:ident : tactic => withMainContext do
  let main ← getMainGoal
  let purchasedWidth ← getFVarFromUserName witness.getId
  let widthClaim ← instantiateMVars (← inferType purchasedWidth)
  let consequence ← instantiateMVars (← main.getType)
  let underWidth ← mkFreshExprSyntheticOpaqueMVar (.forallE `paidPostWidth widthClaim consequence .default)
  main.assign (mkAppN (mkConst ``useCertifiedPostWidth) #[widthClaim, consequence, underWidth, purchasedWidth])
  replaceMainGoal [underWidth.mvarId!]

set_option maxHeartbeats 6500000 in
/-- The original funded attempt's row reads the corrected preclip bits and the ordinary
successor, with both states cast solely by the measured original width equalities. -/
theorem wide_calendar_spill_at
    {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
    (cpu : v.ParentFullCPUs m ell short u δ ξ v.calendarUnit N x)
    (control : SignedSites.CalendarControlRoom (cpu:=cpu))
    (support : v.SelectedReturnSupport m ell short u δ ξ v.calendarUnit v.calendarUnit_rate x)
    (routeAge : v.routingHeight≤x.h)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
    (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
    (height : v.BranchRoleHeight h width)
    (date : Fin (es).length) (a : Attempt) (day : (es).get date=.attempt a)
    (ok : calendarFundedOperand% "ok") (words : calendarFundedOperand% "words")
    (q : calendarFundedOperand% "statesAt") (site : Fin (siteLast h d k+1)) : paidSpillSettlement% [κ,A,C,v,m,ell,short,u,δ,ξ,N,x,cpu,control,support,
    routeAge,prices,pricePos,groupsFit,metadata,lanesFit,buy,e,perm,i,tag,height,date,a,day,ok,words,q,site] := by
  refine forActualSite (siteNumber h d k) (fun numberedSite => settledAtSite numberedSite) ?_ site
  intro vtx
  let site := (whereAt) vtx
  intro exit z
  have key:=v.selectedPreclipCode m ell short u δ ξ unit x cpu perm path date a day
  have archive : ∀n<topMem,atPrune n=checkedOut (v.wideSignedChart h width stock₀) topMem
      (v.wideOrigin h width S ((reader).format.windows.header es (future).code seed) perm) n :=
    calendarCheckoutAtCode (fun encoded => checkedOut (v.wideSignedChart h width stock₀) topMem
      (v.wideOrigin h width S ((reader).format.windows.header es encoded seed) perm))
      key.1 (registeredSpillCheckout% spillRegisters)
  have chartsByCode (printedCode : Bits (CalendarTape.bits sl es)) (sameCode : (future).code=printedCode) :
      let mounted := (b).coreMount perm.symm whereAt order
        (checkedOut (v.wideSignedChart h width stock₀) topMem
          (v.wideOrigin h width S ((reader).format.windows.header es printedCode seed) perm))
      middleWidth=owed+active₀ ∧
        outW=owed+mounted.actual.chordWidths (routeLoad mounted.ordinary spill) := by
    subst printedCode
    exact (cut pos).spill_charts future v.maxBits first date day atPrune archive
  have charts := chartsByCode record key.1
  have output : outW=owed+active₁ := charts.2
  have before:=v.selected_spill_input_width m ell short u δ ξ unit x cpu v.calendarUnit_rate support
    prices pricePos buy groupsFit metadata lanesFit e perm tag path routeAge height date a day
  have yes : (correct).attempt date=true :=
    originalPaidAttemptMarker v h width ell unit v.maxBits first day
  have rightBound (r : Fin (shape).count) : (shape).bits date.succ r≤bound :=
    ((shape).fits date.succ r false).trans (v.wide_outer_lane h width unit
      ((named v.sampler perm.symm v.depth (shape).mark (shape).exclusive (shape).order) (r,false)))
  have earnedPostWidth : installedWidths ends ((shape).bits date.succ)=owed+active₁ := by
    exact ((shape).atWidth date.succ).trans (exit.symm.trans output)
  underCertifiedPostWidth earnedPostWidth
  intro post
  let left:=cast (congrArg (fun T=>State T site) charts.1) z
  let right:=cast (congrArg (fun T=>State T site) (((shape).atWidth date.succ).symm.trans post)) y₀
  let active (side : Bool) := cond side active₁ active₀
  let endpoint (side : Bool) : State (owed+active side) site :=
    Bool.rec (motive:=fun side=>State (owed+active side) site) left right side
  have settle := v.wide_ranked_spill_carry («X»:=Ex) («Y»:=Fin (CalendarTape.bits sl es))
    («Z»:=D ⊕ Fin (HistoryRoles.stride k v.sampler.degree v.wideJobs * bound)) m ell short u δ ξ unit x cpu v.calendarUnit_rate support
    prices pricePos buy groupsFit metadata lanesFit e perm tag path height date (G) rfl vtx owed
  have paidPre := v.recordedPreclipPins m ell short u δ ξ x cpu support routeAge prices pricePos
    groupsFit metadata lanesFit buy e perm i tag height date a day
  have measured := (applyRegisteredPost% (settle endpoint (selectedRankedAttemptBound yes paidPre.1) rightBound
    (selectedRankedAttemptShape yes paidPre.2)) usingPaidPost post) taps (control.spillRead site date)
    (fun t f=>SignedSites.calendar_spill_shelf v m ell short unit cpu date site t (TurnShelf.projection f).1)
    control.lane (fun _=>rfl) e record (Sum.elim (data ok words q) (inner z)) (by
      splitPaidReadSides
      · transferPurchasedIncoming (v.originalOfferOnPaidChart m ell short u δ ξ x cpu support routeAge prices pricePos groupsFit metadata
          lanesFit buy e perm i tag height ok words q date site a day true z (owed+active₀) before)
          across (FundedDate.selectedPreclipPartsForCode (v:=v) («h»:=h) («width»:=width) («size»:=S) (π:=perm)
            («seed»:=seed) (age:=cpu.age) («budget»:=cpu.ready.credit) (small:=cpu.ready.size_le) first inputs bound (owed+active₀) site)
          tables (fun encoded : Bits (CalendarTape.bits sl es) => tableAt encoded)
          registers (registeredSpillOperand% issues from spillRegisters) keys key attempt yes widths paidPre atIncomingState (endpoint false)
      · closePurchasedPositive ((applyCalendarLayoutOperand% completeOriginalRankedPositiveRead
          [κ, A, C, v, m, ell, short, u, δ, ξ, N, x, cpu, support, routeAge, prices, pricePos,
           groupsFit, metadata, lanesFit, buy, e, perm, i, tag, height, date, a, day, ok, words, q, vtx, post, (inner z), left])
          (selectedRankedAttemptBound yes paidPre.1) (selectedRankedAttemptShape yes paidPre.2)))
  have byCode (printedCode : Bits (CalendarTape.bits sl es)) (sameCode : (future).code = printedCode) :
      let mounted := (b).coreMount perm.symm whereAt order
        (checkedOut (v.wideSignedChart h width stock₀) topMem
          (v.wideOrigin h width S ((reader).format.windows.header es printedCode seed) perm))
      ∀ (beforeState : State middleWidth site) (afterState : State outW site)
        (activeBefore : State (owed+active₀) site)
        (activeAfter : State (owed+mounted.actual.chordWidths (routeLoad mounted.ordinary spill)) site),
        HEq beforeState activeBefore → HEq afterState activeAfter →
        LedgerStep.carry (mounted.onlySpill (F:=F) (whereAt).injective (publicChord h d k) spill
          (ProtocolRAMDateSpillRank.spillEnum mounted (wideRouteOrder h d k))) owed site activeBefore activeAfter =
        FeedTransfer.matrix (cut pos).afterMount (whereAt).injective (publicChord h d k)
          (ProtocolRAMDateSpillRank.spillEnum (cut pos).afterMount (wideRouteOrder h d k))
          carry transfer site beforeState afterState := by
    subst printedCode
    exact (cut pos).spill_transfer future v.maxBits first date day atPrune archive site
  finishRegisteredSpill measured through (byCode record key.1 z
    (cast (congrArg (fun chart=>State chart site) exit.symm) y₀) left right (cast_heq _ _).symm
    ((cast_heq _ _).trans (cast_heq _ _).symm))
  usePhysicalVertexRow

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun suggestionSuffixes => "wide_calendar_spill_at" :: suggestionSuffixes

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
