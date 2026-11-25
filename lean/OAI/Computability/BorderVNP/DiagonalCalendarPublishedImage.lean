import OAI.Computability.BorderVNP.DiagonalCalendarPreparedPacket
import OAI.Computability.BorderVNP.PackedFrozenDirectoryPublication

/-! # The routing image and signed controls at the installed publication addresses -/

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

set_option autoImplicit false
set_option maxRecDepth 7000
set_option maxHeartbeats 14000000

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


open Packing.Inherited Packing.Inherited.FrozenTape Shortening.PublicCapacity BorderVNP.Epoch.Round Cover
open EnrichedOuter

attribute [local instance] portFintype
local notation3 (prettyPrint := false) "plan₁" => cal.seed.choose
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
local notation3 (prettyPrint := false) "names₁" => (cal.frozenWitness).routedFine position
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (names₁).Site).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (names₁).Edge).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false
local notation3 (prettyPrint := false) "widths₁" => fun i => Fintype.card (Machine.Guess S (d₁+1)
  (fun _ _ => 60*logWidth (r₁) (l+1)) i)
local notation3 (prettyPrint := false) "slots₁" => fun i => Fintype.equivFin (Machine.Guess S (d₁+1)
  (fun _ _ => 60*logWidth (r₁) (l+1)) i)
local notation3 (prettyPrint := false) "fit₁" => (plan₁).profile_order_fits widths₁ slots₁
local notation3 (prettyPrint := false) "seed₁" v => (plan₁).frozenLeaf (tape₁) (order₁) position cal.frozenWitness tag₁
  sites₁ edges₁ ports₁ v x₁
local notation3 (prettyPrint := false) "geoSeed" => ((plan₁).execute (tape₁) (order₁) position Unit).choose
local notation3 (prettyPrint := false) "code₁" v => (plan₁).compiled.machine.nativeCode (seed₁ v) geoSeed x₁ rfl widths₁ slots₁ fit₁

open Packing.RoutingOutputs

local notation3 (prettyPrint := false) "fresh₁" => (initial₁).next+7*(dir₁).candidates
local notation3 (prettyPrint := false) "actualTask" => cal.frozenTask grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "table₁" => (located₁).raw.reserve ceiling₁
local notation3 (prettyPrint := false) "origin₁" => Allocation.dest fresh₁ cap₁ (table₁).size (located₁).outputs w₁

/-- Every profile return stores the routing table used for publication and
the 37 unreduced controls of the installed signed task, at its actual
physical output address. -/
theorem SignedCalendarAt.frozenSites_publication_image
    (values : (seedBundle tape₁ axes d₁ order₁ position copies₁).Tables F)
    (history : (packHistory (seed₁ values) (plan₁).compiled.machine.epoch T₁).Index)
    {guess clock : ℕ} {body : Code} {pub : Arg → Word w₁} {macros : TeamOpcode.Macros w₁ 8}
    {reg : RoutingISA.Bank w₁} {mem : Memory w₁} {ok : Prop} {resident : (Fin guess → Bool) → Memory w₁ → Prop}
    (paths : ProfilePaths body guess pub macros reg mem ok clock origin₁
      (nativeTableWords table₁ (((code₁ values) history).val)) resident)
    (run : Returns body pub macros reg mem) :
    let cs := CoverScale.sites (Cube D) (EnrichedOuter.depth S (d₁+1) T₁)
    let cables := (boundaryShape S (d₁+1) T₁).edges+4*(R₁+1)*tiles
    let native := (actualTask).withNetwork cs cables
    let ctrl := controlsBase origin₁ native.cube.cables native.cube.cells ((EnrichedOuter.fan (K:=F) (e:=paid) S)^T₁*tiles) ((R₁+1)*tiles)
    cal.frozenPacketImage grid qpos position chart reader chargeFit values history (readings run.val.2.2) ∧
      ∀ i : Fin 37, readings run.val.2.2 (ctrl+i.val)=native.controls i.val := by
  intro cs cables native ctrl
  have address := (located₁).reserved_size
  rw [address] at paths
  have stored := cal.frozenSites_prepared_packet grid qpos position chart reader chargeFit values history paths run
  refine ⟨stored,?_⟩
  have cell : (actualTask).cube.cells=cs := by
    change CoverScale.sites (Cube D) (EnrichedOuter.depth S _ T₁) = _
    dsimp only [cs]
    rw [grid.depth_eq]
  have lines : (actualTask).cube.cables=cables := by
    change (boundary S _ T₁).edges+4*((R₁+1)*CoverScale.sites (Cube D) _) = _
    dsimp only [cables]
    rw [grid.depth_eq,grid.tiles_eq,Nat.mul_assoc]
    rfl
  have same : native=actualTask :=
    (congrArg₂ (actualTask).withNetwork cell.symm lines.symm).trans (SignedTaskArena.Layout.withNetwork_self _)
  intro i
  change readings run.val.2.2 (controlsBase origin₁ cables cs ((EnrichedOuter.fan (K:=F) (e:=paid) S)^T₁*tiles) ((R₁+1)*tiles)+i.val)=_
  rw [address]
  exact (stored.2.1 i).trans (congrArg (fun t : SignedTaskArena.Layout => t.controls i.val) same).symm

open Packing.CellAddressCircuit

private theorem imageAtBase {sites cables ports cells d k w nOld nLive : ℕ}
    {σ : Type*} [Fintype σ] {fields : Fields sites cables ports cells d k w σ}
    {old : Fin nOld → Fin sites} {live : Fin nLive → Fin ports} {branch : σ → Bool}
    {fromAddr toAddr : ℕ} {ram : ℕ → ℕ} (eqn : toAddr=fromAddr)
    (image : Image fields old live branch fromAddr ram) : Image fields old live branch toAddr ram :=
  eqn.symm ▸ image

private noncomputable def originalRoutingImages
    (values : (seedBundle tape₁ axes d₁ order₁ position copies₁).Tables F)
    (history : (packHistory (seed₁ values) (plan₁).compiled.machine.epoch T₁).Index)
    {guess clock : ℕ} {body : Code} {pub : Arg → Word w₁} {macros : TeamOpcode.Macros w₁ 8}
    {reg : RoutingISA.Bank w₁} {mem : Memory w₁} {ok : Prop} {resident : (Fin guess → Bool) → Memory w₁ → Prop}
    (paths : ProfilePaths body guess pub macros reg mem ok clock origin₁
      (nativeTableWords table₁ (((code₁ values) history).val)) resident)
    (run : Returns body pub macros reg mem) :=
  let haveWords := cal.frozenSites_publication_image grid qpos position chart reader chargeFit values history paths run
  let sameAddress := congrArg (fun gates => Allocation.dest fresh₁ cap₁ gates (located₁).outputs w₁) (located₁).reserved_size
  let original := (plan₁).frozen_routing_image tape₁ order₁ position cal.frozenWitness tag₁ sites₁ edges₁ ports₁
    values x₁ history dir₁ grid.sites_pos _ _ _ _ haveWords.1.1
  PLift.up (And.intro (imageAtBase sameAddress haveWords.1.1) (imageAtBase sameAddress original))

/-- The emitted original-slot and live-bit image lies at the actual reserved
table's destination in the RAM of this very return. -/
theorem SignedCalendarAt.frozenSites_native_image
    (values : (seedBundle tape₁ axes d₁ order₁ position copies₁).Tables F)
    (history : (packHistory (seed₁ values) (plan₁).compiled.machine.epoch T₁).Index)
    {guess clock : ℕ} {body : Code} {pub : Arg → Word w₁} {macros : TeamOpcode.Macros w₁ 8}
    {reg : RoutingISA.Bank w₁} {mem : Memory w₁} {ok : Prop} {resident : (Fin guess → Bool) → Memory w₁ → Prop}
    (paths : ProfilePaths body guess pub macros reg mem ok clock origin₁
      (nativeTableWords table₁ (((code₁ values) history).val)) resident)
    (run : Returns body pub macros reg mem) :
    type_of% ((originalRoutingImages cal grid qpos position chart reader chargeFit values history paths run).down.1) :=
  (originalRoutingImages cal grid qpos position chart reader chargeFit values history paths run).down.1

/-- The geometry writer reads those same entries as the original verifier's
site rows and as its live ports, numbered by team and grid tile. -/
theorem SignedCalendarAt.frozenSites_routing_image
    (values : (seedBundle tape₁ axes d₁ order₁ position copies₁).Tables F)
    (history : (packHistory (seed₁ values) (plan₁).compiled.machine.epoch T₁).Index)
    {guess clock : ℕ} {body : Code} {pub : Arg → Word w₁} {macros : TeamOpcode.Macros w₁ 8}
    {reg : RoutingISA.Bank w₁} {mem : Memory w₁} {ok : Prop} {resident : (Fin guess → Bool) → Memory w₁ → Prop}
    (paths : ProfilePaths body guess pub macros reg mem ok clock origin₁
      (nativeTableWords table₁ (((code₁ values) history).val)) resident)
    (run : Returns body pub macros reg mem) :
    type_of% ((originalRoutingImages cal grid qpos position chart reader chargeFit values history paths run).down.2) :=
  (originalRoutingImages cal grid qpos position chart reader chargeFit values history paths run).down.2

end Diagonal

end BorderVNP
end Computability
end OAI
