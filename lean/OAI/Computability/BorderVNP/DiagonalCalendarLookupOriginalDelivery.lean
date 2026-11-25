import OAI.Computability.BorderVNP.DiagonalIssuedEnumerations
import OAI.Computability.BorderVNP.DiagonalSelectedLookupFrameFields
import OAI.Computability.BorderVNP.DiagonalCalendarPhysicalLookup
import OAI.Computability.BorderVNP.DiagonalCalendarScheduledOriginal
import OAI.Computability.BorderVNP.DiagonalOriginalReportParameters

/-! # Original source descriptions on the selected frame's actual delivery -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs.NativeDemands

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical RoutingISA Directory Directory.PrivateBank
open scoped Classical

/-- An occupied original slot in a returned table has its native host and slab offset. -/
theorem originalPairsOfWritten {D C ne np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (dir : Directory.Layout) (old : Fin dir.entries ↪ N.Site)
    (live : (Fin dir.teams × Fin dir.sites) ↪ P) (gap : ℕ)
    {written : ℕ → ℕ × ℕ}
    (recorded : written = privatePair N cell edgeID portID dir old live gap) (j : Fin dir.entries) :
    written j.val = ((cell (old j)).val, (destination N cell edgeID portID dir old live gap (.inl j)).2) :=
  (congrFun recorded j.val).trans (keyPair N cell edgeID portID dir old live gap (.inl j))

open Lean Meta Elab Term in
/-- Retain all native rows and both finite inventories already present in the
projection of an installed private placement table. -/
elab "originalPairsFromReturn%" proof:term:max : term => do
  let held ← elabTerm proof none
  let some eq ← whnfUntil (← inferType held) ``Eq | throwError "expected the native private-placement equality"
  let some rhs ← whnfUntil eq.getAppArgs[2]! ``privatePair | throwError "expected a native original-slot table"
  let rule ← getConstInfo ``originalPairsOfWritten
  forallTelescope rule.type fun bs _ => do
    let some cut ← bs.findIdxM? (fun b => return (← b.fvarId!.getUserName) == `recorded)
      | throwError "missing the written placement equality"
    let some f ← whnfUntil (← inferType bs[cut]!) ``Eq | throwError "expected the table equality"
    let pat := f.getAppArgs[2]!
    let actual := rhs.getAppArgs
    let params ← (bs.extract 0 cut).mapM fun b => do
      if b == f.getAppArgs[1]! then return eq.getAppArgs[1]!
      let some slot := pat.getAppArgs.findIdx? (· == b) | throwError "missing a native original-slot parameter"
      return actual[slot]!
    return mkAppN (Lean.mkConst rule.name rhs.getAppFn.constLevels!) (params.push held)

end Packing.RoutingOutputs.NativeDemands

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA RoutingISA.Evaluator RoutingISA.Transmission RoutingISA.Evaluator.SignedPrep
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Scatter.Assignment JointHeader PackedHistoryCircuit LocalRow Crossing
open DiagonalTallyPacketEmit FiniteEvaluator
open scoped BigOperators

variable {R r t d link inner n w volume : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
    (skeleton : WireLayout (R+1) r link) (header : List Bool) (task : SignedTaskArena.Layout)
    (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    (pin : Fin d → Bool) (guess : Fin (R+1) → ℕ → Bool) (dst ib hb sb : Fin (R+1) → ℕ)
    (frame receivingBase : ℕ) (owner : ℕ → Fin (R+1)) (word : Broadcast task.cube.n task.cube.header.d task.cube.header.cap)
    (pub : HeaderExterior skeleton header → Fin (R+1) → Arg → Word w)
    (mac : HeaderExterior skeleton header → Fin (R+1) → TeamOpcode.Macros w 8)
    (reg : HeaderExterior skeleton header → Fin (R+1) → Bank w) (mem : HeaderExterior skeleton header → Fin (R+1) → Memory w)
    {I : Type*} [Fintype I] (host : I → Fin task.cube.cells) (key : I ↪ ℕ) (sizes : I → ℕ)
    {dim : ℕ} {P A : Type*} {bits : P → ℕ} [Fintype A] (N : Network dim P bits) (cell : N.Site → Fin task.cube.cells)
    (label : Fin task.cube.cells → Label (task.cube.n+1) task.cube.header.d) (recv : A → Fin task.cube.cells) (amount : A → ℕ)

set_option quotPrecheck false
local notation "ar" => task.cube
local notation3 (prettyPrint := false) "decl" => Prod.mk (Fin.ofNat (task.cube.n+1) (readCode (task.cube.n+1) word.1))
  (fun (p : Sym2 (Fin task.cube.header.d)) (j : Fin (task.cube.n+1)) => readCode (task.cube.header.cap+1) (word.2 p j))
local notation3 (prettyPrint := false) "grp" => declaredTeam ar decl label recv amount R
local notation3 (prettyPrint := false) "own" => greedyOwner R task.cube.b task.cube.s label recv amount
local notation "count" => (D.directory pp lp).length
local notation "total" => count+task.cube.header.d.choose 2
local notation "X" => HeaderExterior skeleton header
local notation3 (prettyPrint := false) "PL" u => G.pinLayout u (ib u) (hb u) (sb u)
local notation3 (prettyPrint := false) "BF" u => G.transferFrame u skeleton.header (dst u)

variable (wire : WireLayout (R+1) r link) (same : wire.header=skeleton.header)
local notation3 (prettyPrint := false) "back" => (HeaderExterior.changeLayout skeleton wire same header).symm


set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

local notation3 (prettyPrint := false) "atSite(" x "," u ")" => CandidateSite («X»:=volume) ar D pp lp word owner decl grp frame receivingBase
    (PL u) (G.processorFields u pin (Subtype.val x) (ib u) (hb u) (sb u)) (BF u) (guess u) (pub x u) (mac x u)
    (reg x u) (mem x u) host key sizes N cell recv amount
variable {G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
  pub mac reg mem host key sizes N cell label recv amount wire same}

/-- A receipt on the selected frame uses the same team histories and placements at the
original native directory, bank origin and stride. -/
def PreparationFrame.SelectedLookupSites.receivedOnNativeDirectory
    {F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back)}
    {evidence : ∀ (x : X) (u : Fin (R+1)), atSite(x,u) → Prop}
    (chosen : F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
      pub mac reg mem host key sizes N cell label recv amount wire same evidence)
    (later : WireLayout (R+1) r link) (route : Exterior R r link → Bool)
    (H : Fin (R+1) → TeamHistory w)
    (receipt : ReturnedDelivery G pin route later F.dataDir F.privatePlacement F.livePlacement F.cellOwner
      F.origin F.stride H (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))) :
    ReturnedDelivery G pin route later D F.privatePlacement F.livePlacement F.cellOwner
      (ar).cellBank (ar).cellStride H (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u)) := by
  rw [chosen.projection.directory,chosen.projection.origin,chosen.projection.stride] at receipt
  exact receipt

open Lean Elab Term
open private reachedLookupProjection from OAI.Computability.BorderVNP.DiagonalSelectedLookupProjections

/-- Apply the native-directory transport with the parameters and inventories stored in
this particular returned frame. -/
elab "selectedNativeDelivery% " source:term : term =>
  reachedLookupProjection source ``PreparationFrame.SelectedLookupSites.receivedOnNativeDirectory

end TeamContraction

namespace TeamContraction

open VPVNP.BurstRAM Crossing Packing CellAddresses DiagonalTallyCellReports RoutingISA
open Lean Elab Term Meta

private theorem deliveryAtSameArena {D C w teams : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    {t : SignedTaskArena.Layout} {dir : Directory.Layout} {N : Network D P bits} {cell : N.Site → Fin C}
    {hosts : Fin dir.entries → N.Site} {owner : ℕ → Fin teams} {issued : Fin teams → Memory w}
    {report : ReportLayout} {packets : Fin dir.entries → ReportBundle}
    (receipt : OriginalReportDelivery t dir N cell hosts owner issued report packets) (target : ReportLayout)
    (width : target.fieldWidth = report.fieldWidth) (capacity : target.bodyCap = report.bodyCap) :
    OriginalReportDelivery t dir N cell hosts owner issued target packets :=
  receipt.atReport rfl width capacity

/-- Transfer the supplied bytes to the receiving scanner's layout using the field-width
and body-capacity equalities of this very delivery. -/
elab "originalReportAtLayout%" receipt:term:max " as " target:term:max " with " width:term:max ", " capacity:term:max : term => do
  let original ← elabTerm receipt none
  let some ty ← whnfUntil (← inferType original) ``OriginalReportDelivery |
    throwError "expected a complete original report delivery"
  let .const _ levels := ty.getAppFn | throwError "expected the original report declaration"
  let chosen ← elabTerm target none
  let field ← elabTerm width none
  let body ← elabTerm capacity none
  return mkAppN (mkConst ``deliveryAtSameArena levels) (ty.getAppArgs ++ #[original, chosen, field, body])

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
attribute [local irreducible] stretch Nat.clog UniversalMachine.programPrefix logWidth prefixCapacity
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

local notation "n₁" => l+1
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
local notation3 (prettyPrint := false) "table₁" => (located₁).raw.reserve ceiling₁
local notation "outside₁" => TeamScales.exterior (ξ₁) (r₁) (l+1)
local notation3 (prettyPrint := false) "directory₁" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "fresh₁" => (initial₁).next+7*(directory₁).candidates
local notation3 (prettyPrint := false) "origin₁" =>
  Allocation.dest fresh₁ cap₁ (table₁).size (located₁).outputs w₁
local notation3 (prettyPrint := false) "P₁" => (signedProgram (cube.cubeID paid)).program
local notation3 (prettyPrint := false) "free₁" => (selectedSites).enrichedFree prog₁ P₁ (l+1) ec₁ ℓ₁
local notation3 (prettyPrint := false) "geoSeed" => ((plan₁).execute tape₁ order₁ position Unit).choose
local notation3 (prettyPrint := false) "widths₁" => fun i =>
  Fintype.card (Machine.Guess S (d₁+1) (fun _ _ => 60*logWidth r₁ (l+1)) i)
local notation3 (prettyPrint := false) "slots₁" => fun i =>
  Fintype.equivFin (Machine.Guess S (d₁+1) (fun _ _ => 60*logWidth r₁ (l+1)) i)
local notation3 (prettyPrint := false) "fit₁" => (plan₁).profile_order_fits widths₁ slots₁
local notation3 (prettyPrint := false) "arenaBase" =>
  Allocation.stop ((initial₁).next+7*(dir₁).candidates) cap₁ ceiling₁ (located₁).outputs w₁ w₁
open BorderVNP.Cube.Physical.NativeAssignments DiagonalTallyPacketEmit

local notation3 (prettyPrint := false) "addresses" => reader.deployedReferenceAddresses initial₁ selectedTask directory₁
  (adviceOffsetWith prog₁ r₁ 32 64 w₁ (l+1)) outside₁ fresh₁ cap₁ (table₁).size (located₁).outputs w₁
local notation3 (prettyPrint := false) "hold₁" => cal.frozenRouteBlock chart reader chargeFit
local notation3 (prettyPrint := false) "boots₁" => cal.frozenSites_boots oper.grid qpos position chart reader chargeFit hold₁
local notation3 (prettyPrint := false) "bounds₁" => cal.frozenSpliceBounds oper.grid
local notation3 (prettyPrint := false) "leaf(" v ")" => (plan₁).frozenLeaf tape₁ order₁ position W₁ tag₁ sites₁ edges₁ ports₁ v x₁
local notation3 (prettyPrint := false) "history(" v ")" => (packHistory (leaf(v)) (plan₁).compiled.machine.epoch T₁).Index
local notation3 (prettyPrint := false) "codec(" v ")" => ((plan₁).compiled.machine.nativeCode (leaf(v))
   geoSeed x₁ rfl widths₁ slots₁ fit₁).toEmbedding.trans (Function.Embedding.subtype _)
local notation "identifiers" => paid.Entry ⊕ BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "numberIDs" => (Fintype.equivFin identifiers).toEmbedding.trans Fin.valEmbedding
local notation "qdim" => pairedTableParameters (l+1) size₁+Fintype.card identifiers
local notation3 (prettyPrint := false) "fullPin" h => (boxPinCodec (pairedTableParameters (l+1) size₁) reader.rankFits reader.boxFits).encode h

open JointHeader Routing RoutingISA.Evaluator.SignedPrep CellEntries
local notation3 (prettyPrint := false) "geom₁" =>
  (selectedTask).withNetwork (Fintype.card (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1)))
    ((boundaryShape S (d₁+1) T₁).edges+4*(R₁+1)*tiles)
local notation3 (prettyPrint := false) "planner₁" => cal.frozenPlannerTask oper.grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "elig(" vs "," hist ")" =>
  (plan₁).signedBroadcastAllowed prog₁ (geo₁).fits W₁ position tag₁ sites₁ edges₁ ports₁ vs
    ((geoSeed).eval x₁) (leaf(vs)).property free₁ oper.grid.count (bounds₁).2.1 hist cube scales.α ξ₁
    (bounds₁).1 (geo₁).literalSize (bounds₁).2.2 number₁ (selectedTask).p arenaBase cap₁
local notation3 (prettyPrint := false) "packet(" vs "," hist ")" =>
  (plan₁).signedPackets oper.grid.count tape₁ order₁ position W₁ tag₁ sites₁ edges₁ ports₁ vs
    ((geoSeed).eval x₁) (leaf(vs)).property cube scales.α ξ₁ (bounds₁).1
    (geo₁).literalSize (bounds₁).2.2 (bounds₁).2.1 number₁ (selectedTask).p.privateGap hist
local notation3 (prettyPrint := false) "source(" vs "," hist ")" =>
  (plan₁).signedReportSources (D:=D) (m:=«m») (e:=paid) (S:=S) (R:=R₁) (r:=r₁) (pins:=pins₁)
    (link:=ℓ₁) (k:=l) (d:=d₁) (a:=extra₁) (regs:=64) (rw:=w₁) (ec:=ec₁) (width:=w₁+1)
    (s:=size₁) (copies:=copies₁) (T:=T₁) (header:=header) (work:=Q)
    prog₁ (geo₁).fits W₁ position tag₁ sites₁ edges₁ ports₁ vs ((geoSeed).eval x₁) (leaf(vs)).property
    (fun t i z => ((ExternalSew.RowTrace.seedNumber S (d₁+1) t i) z).val) free₁ oper.grid.count
    (Sum.inl : paid.Entry → identifiers) numberIDs (bounds₁).2.1 hist cube scales.α ξ₁ (bounds₁).1 (geo₁).literalSize
    (bounds₁).2.2 number₁ (selectedTask).p arenaBase cap₁ (fun u => ((selectedSites).publicWords u 0).val)
    (fun _ => origin₁)


private def retainIssuedReportFunction {T : Type} (proof : T) : PSigma (fun returned : Type => returned) :=
  ⟨T,proof⟩

set_option cleanup.letToHave false in
set_option maxRecDepth 18000 in
set_option maxHeartbeats 12000000 in
private noncomputable def SignedCalendarAt.originalDeliveryFunction [Fact (8≤header)] :
    PSigma (fun returned : Type => returned) :=
  let selection := cal.frozenLookupAt oper qpos position chart reader chargeFit
  retainIssuedReportFunction <| fun values h i hist claim raw allowed =>
    let chosen := selection values h i hist claim raw allowed
    let frame := originalLookupFrame% chosen
    let projection := issuedField% projection chosen
    let G := wiringWith prog₁ P₁ selectedSites pins₁ ℓ₁ (l+1) ec₁ (geo₁).fits
    fun (later : Routing.WireLayout (R₁+1) r₁ ℓ₁) (same : (layout₁).header=later.header)
        (wire : Exterior R₁ r₁ ℓ₁ → Bool) (H : Fin (R₁+1) → TeamHistory w₁)
        (receipt : ReturnedDelivery G (fullPin h) wire later (issuedField% dataDir frame)
          (issuedField% privatePlacement frame) (issuedField% livePlacement frame) (issuedField% cellOwner frame)
          (issuedField% origin frame) (issuedField% stride frame) H
          (fun u => G.pinLayout u ((issuedField% inputBase frame) u) ((issuedField% columnBase frame) u)
            ((issuedField% referenceBase frame) u))) (bank : Fin J₁ → ℕ → Bool)
        (target : DiagonalTallyCellReports.ReportLayout) (width : target.fieldWidth=(planner₁).p.siteWidth)
        (capacity : target.bodyCap=(planner₁).p.bodyCap) =>
      let aligned := (cal.frozenPlannerTask_eq oper.grid qpos position chart reader chargeFit).symm.trans
        (cal.frozenEarlyTask oper.grid qpos position chart reader chargeFit)
      let actual := cal.frozenSites_scheduled_original_atTask oper.grid qpos position chart reader chargeFit
        planner₁ aligned (Fact.out (p:=8≤header)) values hist later same (fullPin h) wire
        (issuedField% privatePlacement frame) (issuedField% livePlacement frame) (issuedField% cellOwner frame)
        H (issuedField% inputBase frame) (issuedField% columnBase frame) (issuedField% referenceBase frame)
      let occupied := originalPairsFromReturn% (issuedField% privatePairs projection)
      let returned := (selectedNativeDelivery% chosen) later wire H receipt
      let delivery := actual occupied returned bank
      let scannerWidth := width.trans (congrArg (fun t : SignedTaskArena.Layout => t.p.siteWidth) aligned)
      let scannerCapacity := capacity.trans (congrArg (fun t : SignedTaskArena.Layout => t.p.bodyCap) aligned)
      PLift.up (originalReportAtLayout% delivery as target with scannerWidth, scannerCapacity)

/-- Every returning native history of the selected frame delivers the complete
original descriptions at their registered addresses and within the receiver's
field and opaque-body capacities. -/
noncomputable def SignedCalendarAt.frozenLookupOriginalDelivery [Fact (8≤header)] :=
  (cal.originalDeliveryFunction oper qpos position chart reader chargeFit).2

end Diagonal

end BorderVNP
end Computability
end OAI
