import OAI.Computability.BorderVNP.DiagonalCalendarIssuedPackets
import OAI.Computability.BorderVNP.DiagonalCalendarPreparedNativeNext
import OAI.Computability.BorderVNP.DiagonalNativeSelectedContinuation
import OAI.Computability.BorderVNP.DiagonalGuardedPreparationTransport
import OAI.Computability.BorderVNP.DiagonalSelectedSupportedValueRewrite

/-! # The original guarded column on the attained native candidate plan -/

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
set_option cleanup.letToHave false
set_option maxRecDepth 12000
set_option maxHeartbeats 10000000
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

variable (grid : LocatedSignedGridAt cube b header (l+1)) (qpos : 1 ≤ Q)
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
local notation3 (prettyPrint := false) "located₁" => cal.locatedGateTable grid qpos position (initial₁)
local notation3 (prettyPrint := false) "plan₁" => cal.seed.choose
local notation3 (prettyPrint := false) "W₁" => cal.frozenWitness
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (((W₁).routedFine position).Site)).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (((W₁).routedFine position).Edge)).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "number₁" => Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1))
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false

local notation3 (prettyPrint := false) "selectedTask" => cal.frozenTask grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "selectedSites" => cal.frozenSites grid qpos position chart reader chargeFit
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
local notation3 (prettyPrint := false) "boots₁" => cal.frozenSites_boots grid qpos position chart reader chargeFit hold₁
local notation3 (prettyPrint := false) "bounds₁" => cal.frozenSpliceBounds grid
local notation3 (prettyPrint := false) "leaf(" v ")" => (plan₁).frozenLeaf tape₁ order₁ position W₁ tag₁ sites₁ edges₁ ports₁ v x₁
local notation3 (prettyPrint := false) "history(" v ")" => (packHistory (leaf(v)) (plan₁).compiled.machine.epoch T₁).Index
local notation3 (prettyPrint := false) "codec(" v ")" => ((plan₁).compiled.machine.nativeCode (leaf(v))
   geoSeed x₁ rfl widths₁ slots₁ fit₁).toEmbedding.trans (Function.Embedding.subtype _)
local notation "identifiers" => paid.Entry ⊕ BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "numberIDs" => (Fintype.equivFin identifiers).toEmbedding.trans Fin.valEmbedding
local notation "qdim" => pairedTableParameters (l+1) size₁+Fintype.card identifiers
local notation3 (prettyPrint := false) "fullPin" h => (boxPinCodec (pairedTableParameters (l+1) size₁) reader.rankFits reader.boxFits).encode h

local notation3 (prettyPrint := false) "qp" => Fintype.card (Board.Physical (pairedTableParameters (l+1) size₁)
  (budget₁+6) w₁ (paid.Entry ⊕ BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width))
local notation3 (prettyPrint := false) "gp" => Fintype.card (Guess (Fin (pairedTableParameters (l+1) size₁)) reader.gridRank
  (Nat.clog 2 common.p+1) (Nat.clog 2 common.p))

local notation3 (prettyPrint := false) "realBoot" h:arg =>
  (cal.frozenSites_boots grid qpos position chart reader chargeFit (cal.frozenRouteBlock chart reader chargeFit)).2.choose (fullPin h)
local notation3 (prettyPrint := false) "widthsAt" => Fintype.card identifiers

local notation3 (prettyPrint := false) "wired₁" => CellEntries.SewnTape.wiring (regs:=64) (w:=w₁)
  (ec:=ec₁) (width:=w₁+1) prog₁ (geo₁).fits free₁ pins₁

/-- The packet condition at the native continuation and preparation of one
calendar column. Its completion and observed tally refer to the same candidate. -/
noncomputable abbrev SignedCalendarAt.CandidateGuardedPackets
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁)) (entries : history(values) → ℕ)
    (valid : ∀ (i : Fin pins₁ → Bool) (hist : history(values)) (claim : Fin ((R₁+1)*(qdim)*w₁) → Bool),
      cal.FrozenRouteChecks grid qpos position chart reader chargeFit values h entries i hist claim)
    (next : BootedPinStart.NativeNext (selectedTask).id (realBoot h) (selectedSites).limit.val) : Prop :=
    reader.GuardedPreparedColumn selectedTask initial₁ wired₁ (pub:=(selectedSites).publicWords)
      (regs:=(selectedSites).registers) (args:=addresses) (fullPin h) (realBoot h)
      (selectedSites).limit.val (selectedSites).burst.val le_rfl (fun z u => next z u) cap₁ (selectedTask).cube.header.d
      (selectedTask).cube.header.cap w₁
      (cal.frozenPreparationOnNativeNext grid qpos position chart reader chargeFit values h entries valid next).val

/-- The guarded packet lives on the original issued preparation of the exact
native continuation selected by the physical calls. -/
theorem SignedCalendarAt.frozenGuardedPacketsAtCandidateNext
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    {constraintDir : Packing.Directory.Layout} {ctl res nAxis groups cap wp wd digits outside publicCost localCost fee : ℕ}
    (feasible : (selectedTask).DeployedFeasiblePost initial₁ constraintDir ctl res nAxis groups cap w₁ qp gp reader.gates
      pins₁ r₁ wp wd digits outside publicCost localCost fee (R₁+1) (pairedTableParameters (l+1) size₁) widthsAt)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁)) (entries : history(values) → ℕ)
    (valid : ∀ (i : Fin pins₁ → Bool) (hist : history(values)) (claim : Fin ((R₁+1)*(qdim)*w₁) → Bool),
      cal.FrozenRouteChecks grid qpos position chart reader chargeFit values h entries i hist claim)
    (next : BootedPinStart.NativeNext (selectedTask).id (realBoot h) (selectedSites).limit.val) :
    cal.CandidateGuardedPackets grid qpos position chart reader chargeFit values h entries valid next := by
  let decoder := cal.frozenIssuedHistoryDecoder grid qpos position chart reader chargeFit values (fullPin h)
  let accepted := cal.frozenGuardedPacketsOnIssuedHistory grid qpos position chart reader chargeFit values feasible h
  unfold SignedCalendarAt.CandidateGuardedPackets
  apply reader.preparedPacketsAlong selectedTask initial₁ wired₁ (pub:=(selectedSites).publicWords)
    (regs:=(selectedSites).registers) (args:=addresses) (fullPin h) (realBoot h)
    (selectedSites).limit.val (selectedSites).burst.val le_rfl decoder accepted (fun z u => next z u)
  conv_lhs =>
    unfold SignedCalendarAt.frozenPreparationOnNativeNext SignedCalendarAt.frozenIssuedPreparationAtNext
    issued_preparation_value
  -- Recover the routed inverse already stored in the selected preparation.
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let some (_, lhs, rhs) ← Lean.Meta.matchEq? (← goal.getType) |
      throwError "expected the equality of the two preparations"
    let route (side : Lean.Expr) : Lean.MetaM Lean.Expr := do
      let value ← Lean.Meta.withReducible <| Lean.Meta.whnf side
      let source ← match value.consumeMData with
        | .proj ``Subtype 0 native => pure native
        | e =>
          unless e.getAppFn.isConstOf ``Subtype.val do
            throwError "expected the supported preparation value"
          pure e.appArg!
      let native ← Lean.Meta.withReducible <| Lean.Meta.whnf source
      unless native.getAppFn.isConstOf ``BootedPinStart.PreparedHistoryDecoder.supported do
        throwError "expected the supported history decoder"
      return native.appArg!
    let actual ← route lhs
    let .mvar requested ← route rhs | throwError "expected the undecided routed inverse"
    requested.assign actual
  rfl

end Diagonal

end BorderVNP
end Computability
end OAI
