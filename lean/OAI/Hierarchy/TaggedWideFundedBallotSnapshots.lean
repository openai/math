import OAI.Hierarchy.TaggedWideFundedSelectedReturn
import OAI.Hierarchy.ProbeFixedWideSpillBallotObservation

namespace OAI
/-! # Both processing snapshots on the actual selected paid CPU -/
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
open CoreBoard.HistoryRoles ReportSockets in
private theorem moveLiteralRoleField {h W k jobs N native T : ℕ}
    (model : WideCPU.Dated T) (work : ℕ) (sampler : PurchaseSampler) (perm : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marks : Marks h W k jobs) (exclusive : Exclusive marks) (names : Fin N ≃ Source sampler perm depth marks)
    (qty ids : Fin N → ℕ)
    (volume : model.roleWords = (siteLast h (2^W) k+1) * HistoryRoles.stride k sampler.degree jobs)
    (date : Fin (T+1)) (field : Fin 3) (earlier output : Memory native)
    (low : ∀ i, i < model.rolesEnd work → output i = earlier i)
    (archived : DatedRoleSheets.roleFact model.physical sampler perm depth marks exclusive names
      (model.roleStart work date) qty ids earlier field) :
    DatedRoleSheets.roleFact model.physical sampler perm depth marks exclusive names
      (model.roleStart work date) qty ids output field := by
  apply model.roleFact_local 0 work sampler perm depth marks exclusive names (fun _ => qty) ids volume
    date field earlier output _ archived
  intro i _ hi
  have upper := (WideCPU.role_order model 0 work).upper (finProdFinEquiv (date,field))
  simp only [Equiv.symm_apply_apply] at upper
  exact low i (hi.trans_le upper)

open CoreBoard.HistoryRoles in
open Lean Elab Term in
local elab "afterLiteralDateFields " archived:ident output:ident retained:ident : term => do
  let source ← Meta.getFVarFromUserName archived.getId
  let target ← Meta.getFVarFromUserName output.getId
  let low ← Meta.getFVarFromUserName retained.getId
  Meta.forallBoundedTelescope (← Meta.inferType source) (some 2) fun binders _ => do
    unless binders.size == 2 do throwError "expected the selected date and role field"
    let archivedField := mkAppN source binders
    let typ := (← instantiateMVars (← Meta.inferType archivedField)).consumeMData
    unless typ.isAppOfArity ``DatedRoleSheets.roleFact 18 do
      throwError "expected the original literal role field, found {typ.getAppFn} with {typ.getAppNumArgs} arguments"
    let args := typ.getAppArgs
    let start := args[13]!.consumeMData
    unless start.isAppOfArity ``WideCPU.Dated.roleStart 4 do
      throwError "expected the physical role bank of the source date"
    let bank := start.getAppArgs
    let words ← Meta.mkAppM ``WideCPU.Dated.roleWords #[bank[1]!]
    let volume ← Meta.mkEqRefl words
    let direct := args.extract 1 7 ++ #[bank[0]!, bank[1]!, bank[2]!] ++ args.extract 7 13 ++
      #[args[14]!, args[15]!, volume, binders[0]!, binders[1]!, args[16]!, target, low, archivedField]
    Meta.mkLambdaFVars binders (mkAppN (mkConst ``moveLiteralRoleField) direct)

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
variable (side : Bool) (t : Fin (events v.mesh).length) (a : Attempt) (onDate : (events v.mesh).get t=.attempt a)

open Lean Elab Term in
private partial def exposeSelectedSnapshots (body : Syntax) (entries : List (Name × Lean.Expr))
    (bound values : Array Lean.Expr) : TermElabM Lean.Expr := do
  match entries with
  | [] =>
    let result ← withSynthesize (postpone := .no) <| elabTerm body none
    let result ← instantiateMVars result
    if result.hasExprMVar then throwErrorAt body "unresolved physical input to selected role sheets"
    return result.replaceFVars bound values
  | (id, value) :: more =>
    Meta.withLetDecl id (← Meta.inferType value) value fun localInput =>
      exposeSelectedSnapshots body more (bound.push localInput) (values.push value)

open Lean Elab Term in
local elab "withSelectedSnapshots% " purchase:term ", " sideId:ident ", " dateId:ident ", " attemptId:ident ", " atDate:ident " using " body:term : term => do
  let unpack := fun (fact : Lean.Expr) (op : Name) => do
    let shape ← Meta.whnf (← Meta.inferType fact)
    unless shape.isAppOfArity ``Exists 2 do throwError "expected a selected existential"
    pure (mkAppN (mkConst op shape.getAppFn.constLevels!) (shape.getAppArgs.push fact))
  let evidence := fun v => unpack v ``Exists.choose_spec
  let memory := fun v => unpack v ``Exists.choose
  let left := fun (v : Lean.Expr) => Lean.Expr.proj ``And 0 v
  let right := fun (v : Lean.Expr) => Lean.Expr.proj ``And 1 v
  let purchaseProof ← withSynthesize (postpone := .no) <| elabTerm purchase none
  let purchaseProof ← instantiateMVars purchaseProof
  let observed := left (← evidence (right (right (right purchaseProof))))
  let staged := left (← evidence (← evidence observed))
  let data ← evidence (← evidence (← evidence (← evidence staged)))
  let contents := left (right (right (right (right (right data)))))
  let claim := (← instantiateMVars (← Meta.inferType contents)).consumeMData
  unless claim.isAppOf ``correctedContents do throwError "expected corrected contents from the actual paid return"
  let xs ← #[sideId, dateId, attemptId, atDate].mapM fun id => Meta.getFVarFromUserName id.getId
  let captured := mkAppN (mkConst ``correctedContents.returned_ballot claim.getAppFn.constLevels!)
    (claim.getAppArgs ++ #[contents] ++ xs)
  let before ← memory captured
  let active ← memory (← evidence captured)
  let issued ← evidence (← evidence captured)
  let receipt ← evidence (← evidence observed)
  let checkout := left (right receipt)
  exposeSelectedSnapshots body [(`beforeHeap,before),(`activeHeap,active),(`issuedPages,issued),
    (`pruneArchive,checkout),(`rankLow,left data)] #[] #[]

/- Close adjacent dependent bindings together so each large returned proposition
is abstracted once across their shared local context. -/
open Lean Elab Term in
private partial def elaborateBallotBindings (body : Syntax) (locals : Array Lean.Expr) : TermElabM Lean.Expr := do
  let finish := fun () => do
    let value ← withSynthesize (postpone := .no) <| elabTerm body none
    let value ← instantiateMVars value
    if value.hasExprMVar then throwErrorAt body "unresolved memory argument in the returned ballot"
    let proposition ← instantiateMVars (← Meta.inferType value)
    unless ← Meta.isProp proposition do throwErrorAt body "expected the original ballot proposition"
    let claim ← Meta.mkLetFVars locals proposition (usedLetOnly := true) (generalizeNondepLet := false)
    let complete ← Meta.mkLetFVars locals value (usedLetOnly := true) (generalizeNondepLet := false)
    return mkApp2 (mkConst ``id [.zero]) claim complete
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
    throwErrorAt view.value "unresolved argument while reading ballot field {view.id}"
  Meta.withLetDecl view.id.getId type value fun localValue =>
    elaborateBallotBindings body[i+2] (locals.push localValue)

open Lean Elab Term in
local elab "inferBallotRecord% " body:term : term => elaborateBallotBindings body #[]


abbrev wide_selected_ballot_snapshots := withSelectedSnapshots% bought, side, t, a, onDate using inferBallotRecord%
  let space := support.size.spill cpu.room
  have lower : top ≤ first := (Nat.le_add_right ..).trans space.archiveFloor
  have pages : (g).romEnd rootROM ≤ first := by
    have gap:=space.gap
    have old:=space.oldBefore
    omega
  let rankImage := pruneArchive.frame rankLow lower pages
  have rankAfter : first ≤ rankEnd := by change first ≤ first+_+_; omega
  let beforeImage := rankImage.frame issuedPages.1 (lower.trans rankAfter) (pages.trans rankAfter)
  let processImage := rankImage.frame issuedPages.2.2.1 (lower.trans rankAfter) (pages.trans rankAfter)
  let beforeROM := v.processing_sites x ell unitCost (fun _=>0) _ beforeHeap beforeImage
  let processROM := v.processing_sites x ell unitCost (fun _=>0) _ activeHeap processImage
  let oldShape := And.intro issuedPages.1 (And.intro issuedPages.2.1 (And.intro issuedPages.2.2.1
    (And.intro issuedPages.2.2.2.1 (And.intro issuedPages.2.2.2.2.1 issuedPages.2.2.2.2.2.1))))
  And.intro beforeImage (And.intro beforeROM (And.intro processImage (And.intro processROM oldShape)))


open Lean Elab Term in
local elab "readFinalBallot% " purchase:term "," sideId:ident "," dateId:ident "," attemptId:ident "," atDate:ident : term => do
  let evidence := fun (fact : Lean.Expr) => do
    let shape ← Meta.whnf (← Meta.inferType fact)
    unless shape.isAppOfArity ``Exists 2 do throwError "expected an existential in the selected return"
    pure (mkAppN (mkConst ``Exists.choose_spec shape.getAppFn.constLevels!) (shape.getAppArgs.push fact))
  let right := fun (fact : Lean.Expr) => Lean.Expr.proj ``And 1 fact
  let left := fun (fact : Lean.Expr) => Lean.Expr.proj ``And 0 fact
  let purchaseProof ← withSynthesize (postpone := .no) <| elabTerm purchase none
  let purchaseProof ← instantiateMVars purchaseProof
  if purchaseProof.hasExprMVar then throwError "unresolved selected return argument"
  let observed := left (← evidence (right (right (right purchaseProof))))
  let stages := left (← evidence (← evidence observed))
  let data ← evidence (← evidence (← evidence (← evidence stages)))
  let contents := left (right (right (right (right (right data)))))
  let claim := (← instantiateMVars (← Meta.inferType contents)).consumeMData
  unless claim.isAppOf ``correctedContents do throwError "expected the corrected spill contents"
  let args ← #[sideId, dateId, attemptId, atDate].mapM fun x => Meta.getFVarFromUserName x.getId
  let captured := mkAppN (mkConst ``correctedContents.returned_ballot claim.getAppFn.constLevels!)
    (claim.getAppArgs ++ #[contents] ++ args)
  let issued ← evidence (← evidence captured)
  return right (right (right (right (right (right issued)))))

local notation "returnedBallot" => readFinalBallot% bought, side, t, a, onDate

theorem wide_selected_returned_ballot
    {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
    {N : ℕ} (x : WideParent κ A) (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x)
    (rate : v.sharpPaidUnit≤unitCost) (support : v.SelectedReturnSupport m ell short u δ ξ unitCost rate x)
    (prices : v.PhysicalCounts u A δ ξ m) {C : ℝ} (pricePos : 0≤κ)
    (buy : ∀t:Fin (m+1),Purchased F menu x t slots
      (purchaseCandidates h v.W k v.wideJobs slots ((menu).height t x) (purchaseModules v.W u δ ξ menu x t))
      (purchaseModules v.W u δ ξ menu x t) C)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unitCost≤2^ell)
    {b : Fin k→ℕ} (e : OpenPins h width b→Bool) (perm : Equiv.Perm (Tagged.Row h))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun i=>e (.inl i)))
    (j : Path sl es base)
    (side : Bool) (t : Fin (events v.mesh).length) (a : Attempt) (onDate : (events v.mesh).get t=.attempt a) : type_of% returnedBallot := returnedBallot


private theorem rolesTemporalBound (floorIndex firstSlot rankSlot workStop rolesStop : ℕ)
    (toWork : rolesStop ≤ workStop) (toFloor : workStop+2≤floorIndex)
    (toFirst : floorIndex≤firstSlot) (toRank : firstSlot≤rankSlot) :
    rolesStop≤floorIndex ∧ rolesStop≤firstSlot ∧ rolesStop≤rankSlot := by omega

open Lean Elab Term in
private partial def exposeSelectedRoleParts (body : Syntax) (entries : List (Name × Lean.Expr))
    (bound values : Array Lean.Expr) : TermElabM Lean.Expr := do
  match entries with
  | [] =>
    let result ← withSynthesize (postpone := .no) <| elabTerm body none
    let result ← instantiateMVars result
    if result.hasExprMVar then throwErrorAt body "unresolved physical input to selected role sheets"
    return result.replaceFVars bound values
  | (id, value) :: more =>
    Meta.withLetDecl id (← Meta.inferType value) value fun localInput =>
      exposeSelectedRoleParts body more (bound.push localInput) (values.push value)

open Lean Elab Term in
local elab "withSelectedRoles% " purchase:term ", " sideId:ident ", " dateId:ident ", " attemptId:ident ", " atDate:ident " using " body:term : term => do
  let unpack := fun (fact : Lean.Expr) (op : Name) => do
    let shape ← Meta.whnf (← Meta.inferType fact)
    unless shape.isAppOfArity ``Exists 2 do throwError "expected a selected existential"
    pure (mkAppN (mkConst op shape.getAppFn.constLevels!) (shape.getAppArgs.push fact))
  let evidence := fun v => unpack v ``Exists.choose_spec
  let memory := fun v => unpack v ``Exists.choose
  let left := fun (v : Lean.Expr) => Lean.Expr.proj ``And 0 v
  let right := fun (v : Lean.Expr) => Lean.Expr.proj ``And 1 v
  let purchaseProof ← withSynthesize (postpone := .no) <| elabTerm purchase none
  let purchaseProof ← instantiateMVars purchaseProof
  let observed := left (← evidence (right (right (right purchaseProof))))
  let staged := left (← evidence (← evidence observed))
  let data ← evidence (← evidence (← evidence (← evidence staged)))
  let contents := left (right (right (right (right (right data)))))
  let claim := (← instantiateMVars (← Meta.inferType contents)).consumeMData
  unless claim.isAppOf ``correctedContents do throwError "expected corrected contents from the actual paid return"
  let xs ← #[sideId, dateId, attemptId, atDate].mapM fun id => Meta.getFVarFromUserName id.getId
  let captured := mkAppN (mkConst ``correctedContents.returned_ballot claim.getAppFn.constLevels!)
    (claim.getAppArgs ++ #[contents] ++ xs)
  let before ← memory captured
  let active ← memory (← evidence captured)
  let issued ← evidence (← evidence captured)
  let ranked ← memory staged
  let lowToOriginal ← memory (← evidence observed)
  let literal := left (right (right (right (left (right (right purchaseProof))))))
  exposeSelectedRoleParts body [(`beforeHeap,before),(`activeHeap,active),(`issuedPages,issued),
    (`rankedHeap,ranked),(`rankLow,left data),(`lowToOriginal,lowToOriginal),(`archivedFields,literal)] #[] #[]

local notation "roleWordSize" => Native.wordBits h d Native.copies
local notation "romImage" => v.wideTerminalPreimage x g
  (v.wide_dated_sites h width ell unitCost) (v.wide_dated_edges h width ell unitCost) (fun _=>0)

private abbrev selected_role_images_of_checkouts := withSelectedRoles% bought, side, t, a, onDate using
  fun (topCut : ℕ) (checked : Memory roleWordSize)
      (beforeArchive : ProcessingArchive topCut rootROM ((g).romEnd rootROM) checked romImage beforeHeap)
      (activeArchive : ProcessingArchive topCut rootROM ((g).romEnd rootROM) checked romImage activeHeap) => by
    have roleStop : (g).rolesEnd S ≤ (g).workEnd S := by
      dsimp only [WideCPU.Dated.workEnd,WideCPU.Dated.slotStart,WideCPU.Dated.maskStart,
        WideCPU.Dated.controlStart,WideCPU.endOf]
      omega
    have workStop : (g).workEnd S + 2 ≤ (lay).floor := v.wide_window_after_terminal x _
    have floorStop : (lay).floor ≤ first := by
      have low : (lay).floor ≤ (lay).pruneScratch := Nat.le_add_right _ _
      omega
    have rankAfter : first ≤ rankEnd := by change first ≤ first+_+_; omega
    have bounds:= rolesTemporalBound (lay).floor first rankEnd ((g).workEnd S) ((g).rolesEnd S) roleStop workStop floorStop rankAfter
    let original (mem : Memory roleWordSize) (frame : ∀n,n<rankEnd → mem n=rankedHeap n) :=
      let retained (n) (hn : n<(g).rolesEnd S) :=
        (frame n (hn.trans_le bounds.2.2)).trans
          ((rankLow n (hn.trans_le bounds.2.1)).trans (lowToOriginal n (hn.trans_le bounds.1)))
      afterLiteralDateFields archivedFields mem retained
    let earlierStride := v.processing_stride x ell unitCost (fun _=>0) checked beforeHeap beforeArchive
    let currentStride := v.processing_stride x ell unitCost (fun _=>0) checked activeHeap activeArchive
    let currentRoles := And.intro currentStride (And.intro (original activeHeap issuedPages.2.2.1)
      (corrected_role_pages activeHeap issuedPages.2.2.2.1))
    let earlierRoles := And.intro earlierStride (And.intro (original beforeHeap issuedPages.1)
      (corrected_role_pages beforeHeap issuedPages.2.1))
    exact And.intro currentRoles earlierRoles


open Lean Elab Term in
local elab "rolesFromSelectedSnapshot% " record:term : term => do
  let raw ← withSynthesize (postpone := .no) <| elabTerm record none
  let raw := (← instantiateMVars raw).consumeMData
  unless raw.isAppOf ``wide_selected_ballot_snapshots do throwError "expected selected ballot snapshots"
  let before := Lean.Expr.proj ``And 0 raw
  let current := Lean.Expr.proj ``And 0 (.proj ``And 1 (.proj ``And 1 raw))
  let frame := (← instantiateMVars (← Meta.inferType before)).consumeMData
  unless frame.isAppOfArity ``ProcessingArchive 7 do
    throwError "expected the original processing archive at the pre-control memory"
  let shape := frame.getAppArgs
  return mkAppN (mkConst ``selected_role_images_of_checkouts raw.getAppFn.constLevels!)
    (raw.getAppArgs ++ #[shape[1]!,shape[4]!,before,current])

local notation "selectedRoleImages" => rolesFromSelectedSnapshot%
  (v.wide_selected_ballot_snapshots m ell short u δ ξ unitCost x cpu rate support
     prices pricePos buy groupsFit metadata lanesFit e perm tag j side t a onDate)

theorem wide_selected_role_images
    {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
    {N : ℕ} (x : WideParent κ A) (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x)
    (rate : v.sharpPaidUnit≤unitCost) (support : v.SelectedReturnSupport m ell short u δ ξ unitCost rate x)
    (prices : v.PhysicalCounts u A δ ξ m) {C : ℝ} (pricePos : 0≤κ)
    (buy : ∀t:Fin (m+1),Purchased F menu x t slots
      (purchaseCandidates h v.W k v.wideJobs slots ((menu).height t x) (purchaseModules v.W u δ ξ menu x t))
      (purchaseModules v.W u δ ξ menu x t) C)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unitCost≤2^ell)
    {b : Fin k→ℕ} (e : OpenPins h width b→Bool) (perm : Equiv.Perm (Tagged.Row h))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun i=>e (.inl i)))
    (j : Path sl es base)
    (side : Bool) (t : Fin (events v.mesh).length) (a : Attempt) (onDate : (events v.mesh).get t=.attempt a) : type_of% selectedRoleImages := selectedRoleImages


local notation "checkedRoleImages" => v.wide_selected_role_images m ell short u δ ξ unitCost x cpu rate support prices pricePos buy
    groupsFit metadata lanesFit e perm tag j side t a onDate

theorem wide_selected_processing_roles
    {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
    {N : ℕ} (x : WideParent κ A) (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x)
    (rate : v.sharpPaidUnit≤unitCost) (support : v.SelectedReturnSupport m ell short u δ ξ unitCost rate x)
    (prices : v.PhysicalCounts u A δ ξ m) {C : ℝ} (pricePos : 0≤κ)
    (buy : ∀t:Fin (m+1),Purchased F menu x t slots
      (purchaseCandidates h v.W k v.wideJobs slots ((menu).height t x) (purchaseModules v.W u δ ξ menu x t))
      (purchaseModules v.W u δ ξ menu x t) C)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unitCost≤2^ell)
    {b : Fin k→ℕ} (e : OpenPins h width b→Bool) (perm : Equiv.Perm (Tagged.Row h))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun i=>e (.inl i)))
    (j : Path sl es base)
    (side : Bool) (t : Fin (events v.mesh).length) (a : Attempt) (onDate : (events v.mesh).get t=.attempt a) : type_of% ((checkedRoleImages).1) := (checkedRoleImages).1

theorem wide_selected_control_roles
    {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
    {N : ℕ} (x : WideParent κ A) (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x)
    (rate : v.sharpPaidUnit≤unitCost) (support : v.SelectedReturnSupport m ell short u δ ξ unitCost rate x)
    (prices : v.PhysicalCounts u A δ ξ m) {C : ℝ} (pricePos : 0≤κ)
    (buy : ∀t:Fin (m+1),Purchased F menu x t slots
      (purchaseCandidates h v.W k v.wideJobs slots ((menu).height t x) (purchaseModules v.W u δ ξ menu x t))
      (purchaseModules v.W u δ ξ menu x t) C)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unitCost≤2^ell)
    {b : Fin k→ℕ} (e : OpenPins h width b→Bool) (perm : Equiv.Perm (Tagged.Row h))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun i=>e (.inl i)))
    (j : Path sl es base)
    (side : Bool) (t : Fin (events v.mesh).length) (a : Attempt) (onDate : (events v.mesh).get t=.attempt a) : type_of% ((checkedRoleImages).2) := (checkedRoleImages).2

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wide_selected_ballot_snapshots"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wide_selected_returned_ballot"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wide_selected_role_images"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "selected_role_images_of_checkouts"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wide_selected_processing_roles"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wide_selected_control_roles"

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
