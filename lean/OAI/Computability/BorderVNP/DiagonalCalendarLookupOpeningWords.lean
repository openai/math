import OAI.Computability.BorderVNP.DiagonalSelectedLookupFrameFields
import OAI.Computability.BorderVNP.DiagonalSelectedLookupProjections
import OAI.Computability.BorderVNP.DiagonalIssuedEnumerations
import OAI.Computability.BorderVNP.DiagonalCalendarOpeningBeforeSelection
import OAI.Computability.BorderVNP.DiagonalCalendarSortedOutputWords
import OAI.Computability.BorderVNP.DiagonalCalendarArgumentHeader
import OAI.Computability.BorderVNP.DiagonalCalendarPhysicalLookup
import OAI.Computability.BorderVNP.DiagonalCalendarOpeningFields
import OAI.Computability.BorderVNP.DiagonalCalendarResidentTaskFrame
import OAI.Computability.BorderVNP.DiagonalCalendarPlannerTask
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalChart
import OAI.Computability.BorderVNP.DiagonalCandidateStartupWords

/-! # Opening fields on every physically attained original header exterior -/

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



open Packing.RoutingOutputs


/-- The signed opener's issued words and the original group of argument registers at one physical site. -/
def SignedCalendarAt.LookupOpeningWords
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (hist : history(values)) (u : Fin (R₁+1)) (ram : ℕ → ℕ) : Prop :=
  let t := planner₁
  let frame := ((selectedSites).publicWords u 0).val
  let ptr := bases origin₁ t.cube.cables t.cube.cells (dir₁).entries
  let ctrl := controlsBase origin₁ t.cube.cables t.cube.cells (dir₁).entries ((dir₁).teams*(dir₁).sites)
  (Header frame origin₁ t.cube.cables t.cube.cells (dir₁).entries ram ∧
    (privateLayout frame origin₁ t.cube.cables t.cube.cells (dir₁).entries (dir₁).description t.p.privateGap).Fits w₁ ram ∧
    (∀ j : Fin 37,ram (ctrl+j.val)=t.controls j.val) ∧
    cal.frozenSortedBundleWords oper.grid qpos position chart reader chargeFit values hist ram) ∧
  t.OpenFields u.val frame ptr.ends ctrl ptr.livePairs ((dir₁).teams*(dir₁).sites) (dir₁).entries ram ∧
  ram (frame+30)=w₁ ∧ ram (frame+14)=t.before.limit ∧ ram (frame+89)=(t.tasks 0 0 0 0).tasks

set_option cleanup.letToHave false in
set_option maxRecDepth 15000 in
set_option maxHeartbeats 12000000 in
/-- All original exteriors and teams of the common selected candidate contain the
same original words that the geometry interpreter wrote on their recorded returns. -/
noncomputable def SignedCalendarAt.frozenLookupOpeningWords
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (i : Fin pins₁ → Bool) (hist : history(values)) (claim : Fin ((R₁+1)*(qdim)*w₁) → Bool)
    (raw : CheckedBroadcast (planner₁).cube) (allowed : (elig(values,hist)) raw.val) :
    PSigma (fun p : Prop => p) := by
  let chosen := cal.frozenLookupAt oper qpos position chart reader chargeFit values h i hist claim raw allowed
  let rawSites := issuedField% site chosen
  let rawEvidence := originalLookupAttained% chosen
  have words : ∀ z u, cal.LookupOpeningWords oper qpos position chart reader chargeFit values hist u
      (readings (issuedField% geometry (rawSites z u))) := by
    intro z u
    let reached := rawEvidence z u
    let ret := reached.choose
    let onReturn := reached.choose_spec.1
    let report := reached.choose_spec.2
    have recorded : cal.LookupOpeningWords oper qpos position chart reader chargeFit values hist u (readings ret.val.2.2) :=
      ⟨cal.frozenOpeningStartOfEvidence oper.grid qpos position chart reader chargeFit oper.routing values hist u
          report.2.2.1 report.2.2.2.1 report.2.2.2.2.1 report.2.2.2.2.2,
        cal.frozenOpeningWordsOfResidence oper.grid qpos position chart reader chargeFit oper.routing u report.2.2.1⟩
    exact (congrArg (fun m : Memory w₁ => cal.LookupOpeningWords oper qpos position chart reader chargeFit
      values hist u (readings m)) (issuedField% geometryMemory onReturn)).mpr recorded
  exact ⟨_, words⟩

end Diagonal

end BorderVNP
end Computability
end OAI
