import OAI.Computability.BorderVNP.DiagonalCalendarIssuedBareAt
import OAI.Computability.BorderVNP.DiagonalIssuedEnumerations
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalFieldGeometry
import OAI.Computability.BorderVNP.DiagonalRestoredPublicationState
import OAI.Computability.BorderVNP.DiagonalCalendarArgumentRoutingImage
import OAI.Computability.BorderVNP.DiagonalRoutingHeaderOperands
import OAI.Computability.BorderVNP.DiagonalCalendarArgumentScalars
import OAI.Computability.BorderVNP.DiagonalCalendarArgumentRoom
import OAI.Computability.BorderVNP.DiagonalPlannerArgumentCharge
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalCableCapacity
import OAI.Computability.BorderVNP.DiagonalCalendarMeanOwner
import OAI.Computability.BorderVNP.DiagonalCalendarFinishSortShape
import OAI.Computability.BorderVNP.DiagonalReindexedCandidateArgument
import OAI.Computability.BorderVNP.DiagonalCalendarWriterTopology

/-! # The actual argument and private-call charge on an original selected frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Diagonal.ExternalSew Cover Packing Packing.DeckGrid Crossing Branch Epoch PackedHistoryCircuit
open PackedHistoryCircuit.Normalized SelectedSchedule EnrichedOuter TeamScales TeamContraction ProcessorSlots
open VPVNP ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar
open FieldProcessor RoutingISA RoutingISA.Evaluator RoutingISA.Transmission
open GeometryAdvice GeometryFrameEncoding RoutingISA.Pins VPVNP.BurstRAM RoutingISA.CompactMachine TeamSite
open DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins
open scoped Classical BorderVNP.Epoch.Cube

attribute [local irreducible] stretch Nat.clog logWidth prefixCapacity Fintype.equivFin
  UniversalMachine.programPrefix FieldProcessor.freeWidth
set_option cleanup.letToHave false
set_option maxRecDepth 22000
set_option maxHeartbeats 17000000

open Packing.Inherited Packing.Inherited.FrozenTape Shortening.PublicCapacity BorderVNP.Epoch.Round Cover
open EnrichedOuter CellMacro.Generator RoutingISA.CompactMachine
open Packing.CellAddresses Packing.RoutingOutputs Packing.CellAddressPhysical
open ExternalSew.RowTrace ExternalSew.FieldExport GridHosts Packing.DeckGrid
open CellEntries JointHeader Routing RoutingISA.Evaluator.ScheduleClock TeamContraction.JointHeader
open ResidueIndex ResidueBox

attribute [local instance] portFintype

private theorem headerAboveCables {a b : SignedTaskArena.Layout} {origin : ℕ}
    (same : a=b) (above : origin+3*b.cube.cables ≤ b.cube.header.header) :
    origin+3*a.cube.cables ≤ a.cube.header.header := by
  cases same
  exact above

open Lean Meta Elab Term

/-- Read the parameters of a native receipt from its proved statement. -/
private def originalInputSpine (value : Expr) (head : Name) : TermElabM (NameMap Expr) := do
  let some app ← whnfUntil value head | throwError "expected {head} on the original packet"
  let mut signature := (← getConstInfo head).type
  let mut result : NameMap Expr := {}
  for arg in app.getAppArgs do
    result := result.insert signature.bindingName! arg
    signature := signature.bindingBody!
  return result

private def issuedInputs (proof : Expr) (head : Name) : TermElabM (NameMap Expr) := do
  originalInputSpine (← inferType proof) head

private def assignInputs (result source : NameMap Expr) (fields : Array (Name × Name)) :
    TermElabM (NameMap Expr) := do
  let mut result := result
  for (target, name) in fields do
    let some indexedValue :=  source.find? name | throwError "missing original operand {name} for {target}"
    result := result.insert target indexedValue
  return result

private def originalInstanceNames (head : Name) : TermElabM (Array Name) := do
  let mut signature := (← getConstInfo head).type
  let mut names := #[]
  while signature.isForall do
    if signature.bindingInfo!.isInstImplicit then names := names.push signature.bindingName!
    signature := signature.bindingBody!
  return names

private def originalEnumeration (source : NameMap Expr) (head : Name) : TermElabM Expr := do
  let #[name] ← originalInstanceNames head | throwError "expected one native enumeration in {head}"
  let some enumeration := source.find? name | throwError "missing native enumeration in {head}"
  return enumeration

/-- Compare the library on the registered publication with the same installed
library at the current field's actual boot. -/
local elab "returnedLibrary% " source:term:max raw:term:max current:term:max : term => do
  let site ← elabTerm source none
  let published ← elabTerm raw none
  let node ← elabTerm current none
  let restored ← restoredPinEvidence site published
  let some boot ← whnfUntil (← inferType node) ``BootedPinStart
    | throwError "expected the original field's native boot"
  let installed := mkAppN (← mkConstWithLevelParams ``BootedPinStart.installed_routines_at) (boot.getAppArgs.push node)
  mkEqTrans (← mkEqSymm restored.macros) installed

private def requiredType (name : Name) : Bool :=
  #[`ids, `wordFit, `positive, `liveWidth, `pubAt, `decoded, `team].contains name

private def dynamicInput (name : Name) : Bool :=
  #[`packetBits, `box, `body, `ready, `reported, `fragmentFit, `fragmentCells, `emission, `bank].contains name

-- Construct the nine trailing report binders from the lower theorem's own
-- types. Its physical arguments have already been fixed by the original
-- network, publication, site and returned owner.
private partial def nativeArgumentFunction (app signature : Expr) (prefixArgs bound : Array Expr)
    (known : NameMap Expr) (written : NameMap Syntax) : TermElabM Expr := do
  unless signature.isForall do return ← mkLambdaFVars bound app
  let name := signature.bindingName!
  let domain := signature.bindingDomain!.instantiateRev prefixArgs
  let info := signature.bindingInfo!
  if dynamicInput name then
    withLocalDecl name info domain fun x =>
      nativeArgumentFunction (mkApp app x) signature.bindingBody! (prefixArgs.push x) (bound.push x) known written
  else
    let x ← match known.find? name, written.find? name with
      | some v, none => pure v
      | none, some stx =>
        if name == `header then
          routingHeaderOnOperands (← elabTerm stx none) domain
        else
          elabTerm stx (if requiredType name then some domain else none)
      | none, none =>
        if info.isInstImplicit then synthInstance domain else throwError "no original operand for {name}"
      | _, _ => throwError "duplicate original operand {name}"
    nativeArgumentFunction (mkApp app x) signature.bindingBody! (prefixArgs.push x) bound known written

/-- A named input of the recorded native argument-window theorem. -/
declare_syntax_cat frozenWindowInput

/-- Bind a native operand name to the term read from the original calendar. -/
syntax "(" ident ":=" term ")" : frozenWindowInput

/-- Apply the native argument-window proof using the original four dependent
receipts, in particular the retained header, layout, bank and cardinalities. -/
local elab "nativeArgumentWindow% " reached:term:max chosen:term:max represents:term:max pub:term:max
    controlEq:term:max "[" args:frozenWindowInput* "]" : term => do
  let own ← elabTerm reached none
  let site ← elabTerm chosen none
  let native ← elabTerm represents none
  let published ← elabTerm pub none
  let controlProof ← elabTerm controlEq none
  let ownerFields ← issuedInputs own ``PreparationFrame.ReturnedOwnershipAt
  let siteFields ← issuedInputs site ``SignedPrep.CandidateSite
  let netFields ← issuedInputs native ``Packing.CellAddressPhysical.Represents
  let pubFields ← issuedInputs published ``PublishedPin
  let some privatePairs := siteFields.find? `pp | throwError "missing the returned site's original placements"
  let privateFields ← originalInputSpine privatePairs ``Packing.RoutingOutputs.NativeDemands.privatePair
  let some ctrl ← whnfUntil (← inferType controlProof) ``Eq | throwError "expected the returned site's control address"
  let mut known : NameMap Expr := {}
  known ← assignInputs known ownerFields #[(`R,`R),(`r,`r),(`t,`t),(`pins₀,`d),(`link,`link),(`inner,`inner),
    (`e₀,`n),(`w,`w),(`Edge,`Edge),(`G,`G),(`pin,`pin),(`ext,`exterior),(`L,`L),(`decl,`decl),
    (`template,`template₀),(`count,`count),(`common,`header),(`publicAt,`pub),(`macroAt,`mac),
    (`regAt,`reg),(`memAt,`mem),(`frame,`F),(`seen,`origin),(`routeOwner,`owners),(`q,`v)]
  known ← assignInputs known netFields #[(`D,`D),(`s,`s),(`n,`n),(`d,`d),(`k,`k),(`b,`w),(`P,`P),(`σ,`σ),
    (`bits,`bits),(`N,`N),(`cell,`cell),(`aux,`aux),(`siteID,`siteID),(`edgeID,`edgeID),
    (`portID,`portID),(`F,`F),(`x,`x)]
  known ← assignInputs known siteFields #[(`X,`X),(`word,`word),(`owner,`owner),(`group,`group),(`guess,`guess),
    (`I,`I),(`A,`A),(`host,`host),(`keys,`key),(`sizes,`sizes),(`dest,`recv),(`amount,`amount)]
  -- The publication reads the original-site embedding as a function. Recover
  -- the embedding itself from the original private placement.
  known ← assignInputs known privateFields #[(`original,`old)]
  known ← assignInputs known pubFields #[(`task,`task),(`dir,`dir),(`packetDim,`d),(`bankDim,`g),
    (`live,`live),(`a,`a),(`slotTeam,`u),(`slot,`slot),(`packet,`packet),
    (`origin,`origin),(`gap,`gap),(`bf,`f),(`hdr,`hdr),(`fields,`fields),(`bitsAt,`v),
    (`postPin,`postPin),(`pinMem,`pinMem),(`sourcePub,`pub),(`sourceMac,`mac)]
  known := known.insert `net native |>.insert `site site |>.insert `publication published |>.insert `returned own
    |>.insert `control ctrl.getAppArgs.back! |>.insert `controlAt controlProof
  let mut values : NameMap Syntax := {}
  for arg in args do
    match arg with
    | `(frozenWindowInput| ($n:ident := $e:term)) => values := values.insert n.getId e
    | _ => throwUnsupportedSyntax
  let some imageProof := values.find? `image | throwError "expected the original packet image"
  let imageValue ← elabTerm imageProof none
  let imageFields ← issuedInputs imageValue ``Packing.RoutingOutputs.Image
  values := values.erase `image
  known := known.insert `image imageValue
  let #[portInst, dataInst, siteInst] ← originalInstanceNames ``PreparationFrame.ReturnedOwnershipAt.reindexed_candidate_argument
    | throwError "expected the port, alphabet and site enumerations of the native window"
  known := known.insert portInst (← originalEnumeration pubFields ``PublishedPin)
    |>.insert dataInst (← originalEnumeration imageFields ``Packing.RoutingOutputs.Image)
    |>.insert siteInst (← originalEnumeration siteFields ``SignedPrep.CandidateSite)
  let lower ← mkConstWithLevelParams ``PreparationFrame.ReturnedOwnershipAt.reindexed_candidate_argument
  nativeArgumentFunction lower (← inferType lower) #[] #[] known values

open Lean Meta Elab Term

/-- Recover the calibrated argument list from the type of the real route
checker, retaining its actual parameters and their instances. -/
private def selectionArguments (checks : Expr) : TermElabM (Array Expr) := do
  forallBoundedTelescope (← inferType checks) (some 3) fun _ result => do
    let some enrolled ← whnfUntil result ``SignedCalendarAt.FrozenRouteChecks
      | throwError "expected a checker on the original native pin, history and report"
    let args := enrolled.getAppArgs
    return (args.extract 0 (args.size-3)).push checks

local elab "selectionService% " op:ident checks:term:max : term => do
  let params ← selectionArguments (← elabTerm checks none)
  return mkAppN (← mkConstWithLevelParams (← resolveGlobalConstNoOverload op)) params

local elab "selectionPhysical% " exec:term:max checks:term:max : term => do
  let params ← selectionArguments (← elabTerm checks none)
  let mut decl := (← getConstInfo ``SignedCalendarAt.FrozenRouteChecks).type
  for idx in [:params.size] do
    if decl.bindingName! == `grid then
      let calibrated := params.set! idx (← elabTerm exec none)
      return mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.registeredPhysicalOnOriginalSelection) calibrated
    decl := decl.bindingBody!
  throwError "expected the grid parameter of the operative calendar"

open Lean Meta Elab Term in
local elab "argumentDomain% " service:term:max : term => do
  let applied ← elabTerm service none
  let .forallE _ domain _ _ ← whnf (← inferType applied)
    | throwError "expected a function on original fields or selected frames"
  return domain

/-- Use the candidate site whose actual registers occur in the returned pin
publication. This is the same site's memory read by its routing header. -/
local elab "originalPublishedSite% " receipt:term:max : term => do
  let parameters ← issuedInputs (← elabTerm receipt none) ``PublishedPin
  let some before := parameters.find? `preRegs | throwError "missing native pin registers"
  let site := match before with
    | .proj _ _ candidate => candidate
    | e => e.getAppArgs.back!
  let _ ← issuedInputs site ``SignedPrep.CandidateSite
  return site

/-- The stage certificate and site share the selected lookup, source exterior
and team stored in the pin publication. -/
local elab "originalPublishedStages% " site:term:max : term => do
  let some returned ← whnfUntil (← elabTerm site none) ``PreparationFrame.SelectedLookupSites.returnedSite
    | throwError "expected the native pin's returned candidate site"
  let stages := Lean.mkConst ``PreparationFrame.SelectedLookupSites.returnedSiteStages returned.getAppFn.constLevels!
  return mkAppN stages returned.getAppArgs

/-- The start at each team is already an index of the issued tuple's actual
return. Recover it before comparing the physical header and command words. -/
local elab "originalTeamStarts% " active:term:max : term => do
  let returned ← elabTerm active none
  forallBoundedTelescope (← inferType returned) (some 1) fun teams result => do
    let fields ← originalInputSpine result ``PinStart.Prefix
    let some start := fields.find? `T | throwError "missing original native starting state"
    mkLambdaFVars teams start

local elab "originalNetworkLayout% " same:term:max : term => do
  let some equality ← whnfUntil (← inferType (← elabTerm same none)) ``Eq
    | throwError "expected the planner network equality"
  return equality.getAppArgs[1]!

/-- Abstract the original field, frame and report evidence over the actual
parameters of the enrolled physical service. Both declarations below use this
same native application. -/
private def originalWindowFamily (body : Syntax) : TermElabM Expr := do
  let physical ← mkConstWithLevelParams ``SignedCalendarAt.registeredPhysicalOnOriginalSelection
  let signature ← inferType physical
  withLCtx {} {} <| forallBoundedTelescope signature (some signature.getForallArity) fun xs _ => do
    unless (← xs.back!.fvarId!.getDecl).userName == `valid do
      throwError "expected the original field checker after {xs.size} operands, found {(← xs.back!.fvarId!.getDecl).userName}"
    let proof ← elabTerm body none
    synthesizeSyntheticMVarsNoPostponing
    mkLambdaFVars xs (← instantiateMVars proof)

local elab "originalWindowType% " body:term : term => do
  inferType (← originalWindowFamily body)

open Lean.Elab.Tactic in
local elab "original_window_proof " body:term : tactic => do
  withMainContext do
    (← getMainGoal).assign (← originalWindowFamily body)
    replaceMainGoal []

local macro "declare_original_window " body:term : command => do
  let statement := mkIdent `SignedCalendarAt.OriginalArgumentSelection
  let result := mkIdent `SignedCalendarAt.argumentOnOriginalSelection
  `(section
    /-- The native argument and private-call window on each enrolled original
    field, returned frame, team and sparse report. -/
    def $statement : Prop := originalWindowType% ($body)
    /-- The original returned reports and their measured calls fit the chosen
    signed calendar's argument allowance. -/
    theorem $result : $statement := by original_window_proof ($body)
    end)

declare_original_window
  let originalTuple := selectionService% SignedCalendarAt.issuedBareTupleAtOfCandidates valid
  let deployed := cal.frozenSites_boots oper.grid qpos position chart reader chargeFit
    (cal.frozenRouteBlock chart reader chargeFit)
  let nodes := deployed.2.choose
    ((boxPinCodec (pairedTableParameters (l+1) (stretch b.σ (l+1))) reader.rankFits reader.boxFits).encode h)
  let ownerAt := selectionService% SignedCalendarAt.frozenIssuedOwnershipAtOriginalOfCandidates valid
  let fieldsAt := selectionPhysical% oper valid
  let numeric := cal.frozenPlannerArgumentRate oper.grid qpos position chart reader chargeFit oper.arguments oper.post
  let room := cal.frozenArgumentPublicationRoom oper.grid qpos position chart reader chargeFit oper.routing
  let scalar := cal.frozenArgumentScalars oper.grid qpos position chart reader chargeFit oper.routing
  let sort := cal.frozenPacketSortShape oper.grid position
  let geomToPlanner := cal.frozenPlannerTask_eq oper.grid qpos position chart reader chargeFit
  let taskEq := geomToPlanner.symm.trans (cal.frozenEarlyTask oper.grid qpos position chart reader chargeFit)
  fun (f : argumentDomain% fieldsAt) =>
    let nativeAt := fieldsAt f
    let own := ownerAt f
    let hist := f.2.1
    fun (selected : argumentDomain% nativeAt) (u : Fin (b.physical.teamsPred (l+1)+1)) =>
      let banked := (nativeAt selected u).1
      let site := originalPublishedSite% (banked.2.2)
      let evidence := originalPublishedStages% site
      let retained := evidence.1.choose_spec.1
      letI := site.issuedEnumeration
      let published := restoredPublicationOnReturn% (banked.2.2) site
      let z := originalTuple f
      let U := originalTeamStarts% (z.2)
      let native := (cal.frozenWriterTopology oper.grid qpos position chart reader chargeFit values hist).down
      let cross := cal.originalArgumentPairBound oper qpos position chart reader chargeFit values hist
      let ownerCoordinates := cal.frozenSites_meanOwner oper.grid qpos position chart reader chargeFit values hist
      let keyWidth := (cal.frozenPacketInputs oper.grid position oper.grid.sites_pos).2.1.2.2.2.1
      nativeArgumentWindow% own site (native.1) published (issuedField% controlBase retained) [
        (physical:=originalNetworkLayout% geomToPlanner) (same:=geomToPlanner) (u:=u)
        (ids:=fun _ => rfl) (wireFit:=native.2) (hk:=keyWidth) (wordFit:=le_rfl) (positive:=Fintype.card_pos)
        (liveWidth:=fun _ => rfl) (bounds:=scalar.1) (U:=U) (active:=z.2) (alphabet:=scalar.2.1)
        (pubAt:=rfl) (macAt:=returnedLibrary% site (banked.2.2) (nodes z.1 u)) (header:=banked.1) (image:=issuedArgumentImage% (banked.2.1))
        (scratch:=room.1) (originFit:=room.2.1) (teams:=room.2.2.1) (processors:=room.2.2.2.1)
        (fieldCount:=room.2.2.2.2.1) (literal:=room.2.2.2.2.2.1)
        (cells:=(congrArg (fun a : SignedTaskArena.Layout => a.cube.cells≤2^(b.physical.word (l+1))) taskEq).mpr room.2.2.2.2.2.2.1)
        (stride:=(congrArg (fun a : SignedTaskArena.Layout => a.cube.cellStride≤2^(b.physical.word (l+1))) taskEq).mpr room.2.2.2.2.2.2.2.1)
        (below:=headerAboveCables taskEq room.2.2.2.2.2.2.2.2.1)
        (source:=evidence.2.2.2.2) (decoded:=rfl) (templateFit:=room.2.2.2.2.2.2.2.2.2)
        (team:=rfl) (cap:=cross) (ownerCoordinates:=heq_of_eq ownerCoordinates)
        (p:=sort.1) («d₁»:=sort.2.1) (J:=(cal.frozenPlannerTask oper.grid qpos position chart reader chargeFit).cube.teams) (parameters:=(cal.frozenPlannerTask oper.grid qpos position chart reader chargeFit).p.parameters)
        (expBits:=Nat.clog 2 ((stretch b.ρ (l+1))*(2*l+1)+1)) (budget:=(scales.chosenSignedWindows cube E (l+1) (stretch b.ρ (l+1))).argumentsCalls)
        (Kpos:=scalar.2.2.1) (wpos:=scalar.2.2.2.1) (desc:=scalar.2.2.2.2) (rate:=numeric)]

end Diagonal

end BorderVNP
end Computability
end OAI
