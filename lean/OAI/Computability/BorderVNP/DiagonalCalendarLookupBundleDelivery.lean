import OAI.Computability.BorderVNP.DiagonalIssuedEnumerations
import OAI.Computability.BorderVNP.DiagonalCalendarLookupReportTests
import OAI.Computability.BorderVNP.DiagonalCalendarLookupOriginalDelivery
import OAI.Computability.BorderVNP.DiagonalCalendarLookupFragmentGeometry
import OAI.Computability.BorderVNP.DiagonalReplayOriginalDelivery
import OAI.Computability.BorderVNP.DiagonalSelectedLookupFrameFields

/-! # Delivery to original rows on each returning lookup site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM Crossing Packing CellAddresses DiagonalTallyCellReports RoutingISA
open Lean Meta Elab Term

private theorem atRegisteredOriginalOwner {D C w teams : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    {t : SignedTaskArena.Layout} {dir : Directory.Layout} {N : Network D P bits} {cell : N.Site → Fin C}
    {hosts : Fin dir.entries → N.Site} {owner : ℕ → Fin teams} {issued : Fin teams → Memory w}
    {report : ReportLayout} {packets : Fin dir.entries → ReportBundle}
    (receipt : OriginalReportDelivery t dir N cell hosts owner issued report packets)
    (registered : ℕ → Fin teams) (same : owner = registered) :
    OriginalReportDelivery t dir N cell hosts registered issued report packets := by
  cases same
  exact receipt

universe u

private theorem registeredOwnersAgree {A : Sort u} (left common right : A)
    (written : left = common) (retained : right = common) : left = right :=
  written.trans retained.symm

private def selectedOwnerProof (owner : Expr) : MetaM Expr := do
  let some native ← whnfUntil owner ``PreparationFrame.cellOwner |
    throwError "expected the selected frame's owner table"
  let some frame ← whnfUntil native.getAppArgs.back! ``PreparationFrame.SelectedLookupSites.installedFrame |
    throwError "expected the installed native frame"
  let selection := frame.getAppArgs.back!
  mkProjection (← mkProjection selection `projection) `owned

/-- Use both selected native frames' recorded owner equations, in their original
registrations. This does not compare the two presentations of an entire frame. -/
private def recordedOwnerEquality (left right : Expr) : MetaM Expr := do
  let first ← selectedOwnerProof left
  let second ← selectedOwnerProof right
  let some written ← whnfUntil (← inferType first) ``Eq | throwError "expected the stored source owner equation"
  let some retained ← whnfUntil (← inferType second) ``Eq | throwError "expected the destination owner equation"
  let w := written.getAppArgs
  let r := retained.getAppArgs
  return mkAppN (mkConst ``registeredOwnersAgree written.getAppFn.constLevels!) #[w[0]!,w[1]!,w[2]!,r[1]!,first,second]

/-- Restate a received report at the exact required owner, using both recorded
owner equations. The equality comes from the two native writers. -/
private def atRecordedReportOwner (original wantedOwner : Expr) : MetaM Expr := do
  let some rows ← whnfUntil (← inferType original) ``OriginalReportDelivery | throwError "expected the received original reports"
  let signature ← getConstInfo ``OriginalReportDelivery
  let index ← forallTelescope signature.type fun binders _ => do
    let names ← binders.mapM fun b => b.fvarId!.getUserName
    let some index := names.idxOf? `owner | throwError "missing report owner"
    return index
  let own ← recordedOwnerEquality rows.getAppArgs[index]! wantedOwner
  return mkAppN (mkConst ``atRegisteredOriginalOwner rows.getAppFn.constLevels!)
    (rows.getAppArgs ++ #[original,wantedOwner,own])

private theorem agreeOnFour {A B C D E : Type} (f g : A → B → C → D → E)
    (a₁ a₂ : A) (b₁ b₂ : B) (c₁ c₂ : C) (d₁ d₂ : D)
    (fn : f=g) (ha : a₁=a₂) (hb : b₁=b₂) (hc : c₁=c₂) (hd : d₁=d₂) :
    f a₁ b₁ c₁ d₁ = g a₂ b₂ c₂ d₂ := by
  cases fn
  cases ha
  cases hb
  cases hc
  cases hd
  rfl

private theorem atOriginalPackets {D C w teams : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    {t : SignedTaskArena.Layout} {dir : Directory.Layout} {N : Network D P bits} {cell : N.Site → Fin C}
    {hosts : Fin dir.entries → N.Site} {owner : ℕ → Fin teams} {issued : Fin teams → Memory w}
    {report : ReportLayout} {packets : Fin dir.entries → ReportBundle}
    (receipt : OriginalReportDelivery t dir N cell hosts owner issued report packets)
    (registered : Fin dir.entries → ReportBundle) (same : ∀ j, packets j=registered j) :
    OriginalReportDelivery t dir N cell hosts owner issued report registered := by
  cases funext same
  exact receipt

-- The header uses the native tile, slot, host base and multiplicity. The
-- packet uses that header together with the original body, factors and marks.
private def fourPacketFields (left right : Expr) (first : Option Expr := none) : MetaM Expr := do
  let largs := left.getAppArgs
  let rargs := right.getAppArgs
  let lprefix := mkAppN left.getAppFn (largs.extract 0 (largs.size-4))
  let rprefix := mkAppN right.getAppFn (rargs.extract 0 (rargs.size-4))
  let l := largs.extract (largs.size-4) largs.size
  let r := rargs.extract (rargs.size-4) rargs.size
  let types ← l.mapM inferType
  let mut params := types ++ #[← inferType left,lprefix,rprefix]
  for i in [:4] do params := params ++ #[l[i]!,r[i]!]
  let hs ← l.mapM mkEqRefl
  let equal := match first with | some h => hs.set! 0 h | none => hs
  return mkAppN (mkConst ``agreeOnFour) (params ++ #[← mkEqRefl lprefix] ++ equal)

/-- Change the packet function by proving equality at each original ordinal.
Its calibrated slot and base remain explicit arguments to the header equality. -/
private def atPointwiseOriginalPackets (delivered goal : Expr) : MetaM Expr := do
  let some actual ← whnfUntil (← inferType delivered) ``OriginalReportDelivery | throwError "expected original packet bytes"
  let some needed ← whnfUntil goal ``OriginalReportDelivery | throwError "expected original receiving rows"
  let before := actual.getAppArgs.back!
  let target := needed.getAppArgs.back!
  let pointwise ← forallBoundedTelescope (← inferType target) (some 1) fun ordinals _ => do
    let some lhs ← whnfUntil (mkAppN before ordinals) ``BottomReports.physicalBundle | throwError "expected the native marked packet"
    let some rhs ← whnfUntil (mkAppN target ordinals) ``BottomReports.physicalBundle | throwError "expected the registered marked packet"
    let some oldHeader ← whnfUntil lhs.getAppArgs[0]! ``DeckGrid.WiredWitness.seedUseHeader | throwError "expected the native header"
    let some newHeader ← whnfUntil rhs.getAppArgs[0]! ``DeckGrid.WiredWitness.seedUseHeader | throwError "expected the registered header"
    let header ← fourPacketFields oldHeader newHeader
    let row ← fourPacketFields lhs rhs header
    mkLambdaFVars ordinals row
  return mkAppN (mkConst ``atOriginalPackets actual.getAppFn.constLevels!)
    (actual.getAppArgs ++ #[delivered,target,pointwise])

end TeamContraction

namespace Diagonal

open Diagonal.ExternalSew Cover Packing Packing.DeckGrid Crossing Branch Epoch PackedHistoryCircuit
open PackedHistoryCircuit.Normalized SelectedSchedule EnrichedOuter TeamScales TeamContraction ProcessorSlots
open VPVNP ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar
open FieldProcessor RoutingISA RoutingISA.Evaluator RoutingISA.Transmission
open GeometryAdvice GeometryFrameEncoding RoutingISA.Pins VPVNP.BurstRAM RoutingISA.CompactMachine TeamSite
open DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins
open Diagonal.ExternalSew GridHosts
open scoped Classical BorderVNP.Epoch.Cube


open Packing.Inherited Packing.Inherited.FrozenTape Shortening.PublicCapacity BorderVNP.Epoch.Round
open ResidueIndex ResidueBox
attribute [local instance] portFintype
attribute [local irreducible] Nat.clog UniversalMachine.programPrefix logWidth prefixCapacity
  FieldProcessor.freeWidth Fintype.equivFin
set_option maxRecDepth 8200
set_option maxHeartbeats 4400000
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {paid : PaidIdentity F D m}
    {S : SiteSchedule paid} {cube : FixedCube K} {extra E p Q breadth sourcePower : ℕ}
    {scales : EpochScales S (cube.pred+1) extra}
    {b : JointSchedule.{0} scales (E+1) (max (5*(E+2)) p) Q 3076 (breadth+10) (sourcePower+1)}
    {φ : K →+* F} {q : ℕ} {hm : 0 < «m»} {header C A₀ a B₀ b₀ J j coeff addr power cut : ℕ}
    {adv : ℕ → ℕ} {c charge factor l : ℕ}
    (cal : SignedCalendarAt cube b φ q hm header C A₀ a B₀ b₀ J j coeff addr power cut adv c charge factor (l+1))

local notation "r₁" => stretch b.ρ (l+1)
local notation "size₁" => stretch b.σ (l+1)
local notation "R₁" => b.physical.teamsPred (l+1)
local notation "w₁" => b.physical.word (l+1)
local notation "ξ₁" => (scales.τ:ℝ)/5
local notation "ℓ₁" => TeamScales.link (ξ₁) (R₁+1) (l+1)
local notation "ec₁" => Wires.sortExponent (block (ξ₁) (l+1))
local notation "budget₁" => adv (adviceScale b.σ b.ρ (l+1))
local notation "pins₁" => (pairedTableParameters (l+1) (size₁)+2)*(budget₁+6)
local notation "d₁" => CoverScale.initialDepth (Cube D) (r₁) (l+1)-1
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes (d₁)
local notation3 (prettyPrint := false) "order₁" => (Fintype.equivFin (Fin axes → Deck (d₁+2))).symm
local notation3 (prettyPrint := false) "geo₁" => cal.sites.choose
local notation3 (prettyPrint := false) "prog₁" => cube.signedSiteProgram paid
local notation "a₁" => FieldProcessor.freeWidth (prog₁) scales.α 32 64 (r₁) (w₁) (l+1)
local notation "extra₁" => setupWidth (w₁+1) (l+1)+(prefixCapacity (r₁) 32 64 (w₁) (l+1)+1+a₁)
local notation3 (prettyPrint := false) "tape₁" => tapeTemplate (R:=R₁) (r:=r₁) (link:=ℓ₁) (regs:=64) (w:=w₁)
  (e:=ec₁) (width:=w₁+1) (k:=l) (a:=extra₁) (prog₁) (geo₁).fits (pins₁)

variable (oper : FrozenExecutionAt cube b φ q adv c charge header (hm:=hm) (l+1)) (qpos : 1 ≤ Q)
    (position : (Fin (Fintype.card (Cube D)) → Deck (CoverScale.initialDepth (Cube D)
      (stretch b.ρ (l+1)) (l+1)-1+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
local notation "T₁" => epochs scales.τ (l+1)
local notation "copies₁" => TeamScales.width (l+1) scales.α
local notation "J₁" => (fan S)^T₁*tiles
local notation "description" => seedDescriptionWidth (l+1) (r₁) axes (d₁) (header*logWidth (r₁) (l+1))
  (BottomGridBank.bodyBudget (seedBoxCapacity (l+1) (r₁) axes (d₁) (Fintype.card (Direction axes))))
local notation "cap₁" => SeedPlan.profileReserve (r₁) (l+1)
local notation "ceiling₁" => geometryGateCeiling (8*(11920000+1500000+16008100*coeff+37)) (4*(E+2)) (r₁) (l+1)
local notation3 (prettyPrint := false) "dir₁" => freeDirectory (R₁) (r₁)
  ((tape₁).program.length+(cutWidth (l+1)+extra₁)) (ℓ₁) tiles (GridHosts.inputBlockWidth (r₁) (l+1) axes (d₁)) J₁ description

variable {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField paid (φ ∘ cube.table) q l (stretch b.σ (l+1)) ord}
    (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (b.physical.teamsPred (l+1)+1) (stretch b.ρ (l+1))
      (b.physical.multBits (l+1)) (b.physical.tally (l+1)) (b.physical.word (l+1))
      (adv (adviceScale b.σ b.ρ (l+1))+6))
    (chargeFit : reader.charge ≤ c*(adv (adviceScale b.σ b.ρ (l+1))+1)^charge)


local notation3 (prettyPrint := false) "layout₁" => cal.frozenLayout chart reader chargeFit
local notation3 (prettyPrint := false) "initial₁" => reader.startupArenaWith (n:=l+1) (reg:=64)
  (prog₁) (a₁) (ℓ₁) (layout₁).header
local notation3 (prettyPrint := false) "located₁" => cal.locatedGateTable oper.grid qpos position (initial₁)
local notation3 (prettyPrint := false) "plan₁" => cal.seed.choose
local notation3 (prettyPrint := false) "W₁" => cal.frozenWitness
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (((W₁).routedFine position).Site)).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (((W₁).routedFine position).Edge)).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "number₁" => Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1))
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false

local notation3 (prettyPrint := false) "selectedTask" => cal.frozenTask oper.grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "selectedSites" => cal.frozenSites oper.grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "P₁" => (signedProgram (cube.cubeID paid)).program
local notation3 (prettyPrint := false) "free₁" => (selectedSites).enrichedFree prog₁ P₁ (l+1) ec₁ ℓ₁
local notation3 (prettyPrint := false) "geoSeed" => ((plan₁).execute tape₁ order₁ position Unit).choose
local notation3 (prettyPrint := false) "arenaBase" =>
  Allocation.stop ((initial₁).next+7*(dir₁).candidates) cap₁ ceiling₁ (located₁).outputs w₁ w₁
open BorderVNP.Cube.Physical.NativeAssignments DiagonalTallyPacketEmit

local notation3 (prettyPrint := false) "bounds₁" => cal.frozenSpliceBounds oper.grid
local notation3 (prettyPrint := false) "leaf(" v ")" => (plan₁).frozenLeaf tape₁ order₁ position W₁ tag₁ sites₁ edges₁ ports₁ v x₁
local notation3 (prettyPrint := false) "history(" v ")" => (packHistory (leaf(v)) (plan₁).compiled.machine.epoch T₁).Index
local notation "identifiers" => paid.Entry ⊕ BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width
local notation "qdim" => pairedTableParameters (l+1) size₁+Fintype.card identifiers

open JointHeader Routing RoutingISA.Evaluator.SignedPrep CellEntries
local notation3 (prettyPrint := false) "planner₁" => cal.frozenPlannerTask oper.grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "elig(" vs "," hist ")" =>
  (plan₁).signedBroadcastAllowed prog₁ (geo₁).fits W₁ position tag₁ sites₁ edges₁ ports₁ vs
    ((geoSeed).eval x₁) (leaf(vs)).property free₁ oper.grid.count (bounds₁).2.1 hist cube scales.α ξ₁
    (bounds₁).1 (geo₁).literalSize (bounds₁).2.2 number₁ (selectedTask).p arenaBase cap₁

private theorem headerAtOriginal {source frame origin cables cells entries : ℕ} {words : ℕ → ℕ}
    (same : source = frame) (read : Packing.RoutingOutputs.Header frame origin cables cells entries words) :
    Packing.RoutingOutputs.Header source origin cables cells entries words :=
  same.symm ▸ read

open Lean Meta Elab Term in
/-- Read the retained geometric header at the origin of its selected site's public bank. -/
local elab "returnedReplayHeaders%" chosen:term:max recorded:term:max : term => do
  let sites ← elabTerm (← `(originalLookupSites% $chosen)) none
  let geometry ← elabTerm recorded none
  forallBoundedTelescope (← inferType sites) (some 2) fun coords _ => do
    let row := mkAppN geometry coords
    let counts ← mkProjection row `right
    let room ← mkProjection counts `right
    let header ← mkProjection room `right
    let origin ← mkProjection (mkAppN sites coords) `origin
    let read ← mkAppM ``headerAtOriginal #[origin,header]
    mkLambdaFVars coords read

open Lean Meta in
private def reportParameter (application : Expr) (field : Name) : MetaM Expr := do
  let info ← getConstInfo application.getAppFn.constName!
  forallTelescope info.type fun binders _ => do
    let names ← binders.mapM fun b => b.fvarId!.getUserName
    let some index := names.idxOf? field | throwError "missing report parameter {field}"
    return application.getAppArgs[index]!

open Lean Meta in
-- Apply the original-row theorem at the fields of the authentic native receipt.
private def receivedOriginalAt (supply extent receipt goal : Expr) : MetaM Expr := do
  let some physical ← whnfUntil (← inferType receipt) ``ReturnedDelivery
    | throwError "expected the returned receiving banks"
  let some required ← whnfUntil goal ``OriginalReportDelivery
    | throwError "expected the original rows on this replay"
  let supply := mkAppN supply #[← reportParameter physical `L,extent,← reportParameter physical `ext,
    ← reportParameter physical `H,receipt]
  let .forallE _ bankType _ _ ← whnfForall (← inferType supply)
    | throwError "expected the original row's mark bank"
  let bank ← forallBoundedTelescope bankType (some 2) fun indices _ => mkLambdaFVars indices (mkConst ``Bool.false)
  let mut supplied := mkApp2 supply bank (← reportParameter required `report)
  -- The field width and opaque body capacity are the two projections of the installed report layout.
  for _ in [:2] do
    let .forallE _ equality _ _ ← whnfForall (← inferType supplied)
      | throwError "expected a physical report width"
    let some (_,installedWidth,_) := equality.eq? | throwError "expected equality of report widths"
    supplied := mkApp supplied (← mkEqRefl installedWidth)
  let original ← mkProjection supplied `down
  let some rows ← whnfUntil (← inferType original) ``OriginalReportDelivery
    | throwError "expected the received originals at the selected task"
  let material := mkAppN (mkConst ``OriginalReportDelivery.onCube rows.getAppFn.constLevels!) (rows.getAppArgs.push original)
  let marked ← atPointwiseOriginalPackets material required
  atRecordedReportOwner marked (← reportParameter required `owner)

private def keepReplayProof {P : Prop} (proof : P) : PSigma (fun Q : Prop => Q) := ⟨P,proof⟩

open Lean Meta in
private def reportRuleAt (report : Expr) : MetaM Expr := do
  let some stage ← whnfUntil report ``PreparationFrame.ReportTest
    | throwError "expected the selected writer's report predicate"
  return mkAppN (mkConst ``PreparationFrame.bundleDeliveryOnReplay stage.getAppFn.constLevels!) stage.getAppArgs.pop

open Lean Meta Elab Term in
/-- Construct the full original-row callback on the native history quantifiers of the actual publication. -/
local elab "acquiredReplayRows%" stage:term:max original:term:max chosen:term:max : term => do
  let rule ← reportRuleAt (← elabTerm stage none)
  let issuedType ← forallBoundedTelescope (← inferType rule) (some 7) fun premises _ => do
    unless premises.size == 7 do throwError "expected the original report's seven inputs"
    inferType premises.back!
  let supply ← elabTerm original none
  let extent ← elabTerm (← `(originalLookupHeader% $chosen)) none
  forallTelescopeReducing issuedType fun coords required => do
    unless coords.size ≥ 2 do throwError "expected the returned delivery and receiving team"
    let rows ← receivedOriginalAt supply extent coords[coords.size-2]! required
    mkLambdaFVars coords rows

open Lean Meta Elab Term in
/-- The same report rule takes its calibrated headers and received originals directly from this replay. -/
local elab "originalReplayDelivery%" published:term:max cap:term:max opened:term:max owner:term:max
    headerRead:term:max issued:term:max : term => do
  let publication ← elabTerm published none
  let rule ← reportRuleAt (← inferType publication)
  let started := mkApp3 rule publication (← elabTerm cap none) (← elabTerm opened none)
  let .forallE _ addressType _ _ ← whnfForall (← inferType started) | throwError "expected the original host address"
  let some (_,hosts,_) := addressType.eq? | throwError "expected the original host address equality"
  return mkAppN started #[← mkEqRefl hosts,← elabTerm owner none,← elabTerm headerRead none,← elabTerm issued none]

set_option maxRecDepth 14000 in
set_option maxHeartbeats 12000000 in
set_option cleanup.letToHave false in
/-- The routing header at each returned original site of this lookup. -/
private noncomputable def SignedCalendarAt.retainedReplayHeaders
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (i : Fin pins₁ → Bool) (hist : history(values)) (claim : Fin ((R₁+1)*(qdim)*w₁) → Bool)
    (raw : CheckedBroadcast (planner₁).cube) (allowed : (elig(values,hist)) raw.val)
    : PSigma (fun Q : Prop => Q) :=
  let lookup := cal.frozenLookupAt oper qpos position chart reader chargeFit values h i hist claim raw allowed
  let geometry := cal.frozenLookupFragmentGeometry oper qpos position chart reader chargeFit values h i hist claim raw allowed
  ⟨_, returnedReplayHeaders% lookup geometry⟩

set_option maxRecDepth 18000 in
set_option maxHeartbeats 32000000 in
set_option cleanup.letToHave false in
/-- The native history's originals at each returned team and every operand of the replay. -/
private noncomputable def SignedCalendarAt.retainedOriginalRows [Fact (8≤header)]
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (i : Fin pins₁ → Bool) (hist : history(values)) (claim : Fin ((R₁+1)*(qdim)*w₁) → Bool)
    (raw : CheckedBroadcast (planner₁).cube) (allowed : (elig(values,hist)) raw.val)
    : PSigma (fun Q : Prop => Q) :=
  let lookup := cal.frozenLookupAt oper qpos position chart reader chargeFit values h i hist claim raw allowed
  let original := cal.frozenLookupOriginalDelivery oper qpos position chart reader chargeFit values h i hist claim raw allowed
  let stage := cal.LookupBundleDeliveryAt oper qpos position chart reader chargeFit values h i hist claim raw allowed
  keepReplayProof (acquiredReplayRows% stage original lookup)

set_option maxRecDepth 18000 in
set_option maxHeartbeats 32000000 in
set_option cleanup.letToHave false in
private noncomputable def SignedCalendarAt.returnedOriginalDeliveryFunction [Fact (8≤header)] :
    PSigma (fun Q : Prop => Q) :=
  let selection := cal.frozenLookupAt oper qpos position chart reader chargeFit
  let retained := cal.retainedReplayHeaders oper qpos position chart reader chargeFit
  let source := cal.retainedOriginalRows oper qpos position chart reader chargeFit
  keepReplayProof <| fun
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (i : Fin pins₁ → Bool) (hist : history(values)) (claim : Fin ((R₁+1)*(qdim)*w₁) → Bool)
    (raw : CheckedBroadcast (planner₁).cube) (allowed : (elig(values,hist)) raw.val)
    (publication : cal.LookupReportPublicationAt oper qpos position chart reader chargeFit values h i hist claim raw allowed)
    (capacity : cal.LookupReportCapacityAt oper qpos position chart reader chargeFit values h i hist claim raw allowed)
    (opening : cal.LookupReportOpeningAt oper qpos position chart reader chargeFit values h i hist claim raw allowed) =>
    let lookup := selection values h i hist claim raw allowed
    let projection := issuedField% projection lookup
    let headers := (retained values h i hist claim raw allowed).2
    let originals := (source values h i hist claim raw allowed).2
    originalReplayDelivery% publication capacity opening (issuedField% owned projection) headers originals

/-- Each original in a visited physical row is delivered at its published slot and
fits the row's signed layout. The proof uses the header on this same replay. -/
theorem SignedCalendarAt.frozenLookupBundleDelivery [Fact (8≤header)] :
    (cal.returnedOriginalDeliveryFunction oper qpos position chart reader chargeFit).1 :=
  (cal.returnedOriginalDeliveryFunction oper qpos position chart reader chargeFit).2

end Diagonal

end BorderVNP
end Computability
end OAI
