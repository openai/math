import OAI.Computability.BorderVNP.DiagonalCalendarNumberedPrivateFields
import OAI.Computability.BorderVNP.DiagonalCalendarNativePublicationPlacement

/-! # The selected frame's report publication from its attained geometry and placement -/

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
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false

local notation3 (prettyPrint := false) "selectedTask" => cal.frozenTask grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "table₁" => (located₁).raw.reserve ceiling₁
local notation "outside₁" => TeamScales.exterior (ξ₁) (r₁) (l+1)
local notation3 (prettyPrint := false) "directory₁" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "fresh₁" => (initial₁).next+7*(directory₁).candidates
local notation3 (prettyPrint := false) "origin₁" =>
  Allocation.dest fresh₁ cap₁ (table₁).size (located₁).outputs w₁
open BorderVNP.Cube.Physical.NativeAssignments DiagonalTallyPacketEmit

local notation3 (prettyPrint := false) "leaf(" v ")" => (plan₁).frozenLeaf tape₁ order₁ position W₁ tag₁ sites₁ edges₁ ports₁ v x₁
local notation3 (prettyPrint := false) "history(" v ")" => (packHistory (leaf(v)) (plan₁).compiled.machine.epoch T₁).Index

open JointHeader Routing RoutingISA.Evaluator.SignedPrep Packing.RoutingOutputs VPVNP.VerifierNetwork
local notation3 (prettyPrint := false) "planner₁" => cal.frozenPlannerTask grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "geometry₁" => (selectedTask).withNetwork
  (Fintype.card (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1)))
  ((boundaryShape S (d₁+1) T₁).edges+4*(R₁+1)*tiles)
local notation3 (prettyPrint := false) "nativePin" => SignedTaskArena.rawAddress initial₁ (geometry₁).cube.header.profile
  (geometry₁).cube.n (geometry₁).cube.header.d (geometry₁).cube.header.cap
local notation3 (prettyPrint := false) "tabs" => bases origin₁ (planner₁).cube.cables (planner₁).cube.cells (dir₁).entries
local notation3 (prettyPrint := false) "controlsAt" => controlsBase origin₁ (planner₁).cube.cables (planner₁).cube.cells
  (dir₁).entries ((dir₁).teams*(dir₁).sites)
local notation3 (prettyPrint := false) "rankDepth" => BottomReports.BundleSort.markedDepth (planner₁).cube.cells (dir₁).entries

/-- Publication on every admissible typed site and preparation frame of the
frozen calendar, using its physical placements and terminal geometry. -/
noncomputable def SignedCalendarAt.SiteReportPublicationAt.{u} : Prop :=
  ∀
    (values : (seedBundle tape₁ axes d₁ order₁ position copies₁).Tables F) (hist : history(values))
    {X : ℕ} {wire : WireLayout (R₁+1) r₁ ℓ₁} {broadcastHeader : List Bool} {pin : Fin pins₁ → Bool}
    {pub : HeaderExterior wire broadcastHeader → Fin (R₁+1) → Arg → Word w₁}
    {mac : HeaderExterior wire broadcastHeader → Fin (R₁+1) → TeamOpcode.Macros w₁ 8}
    {reg : HeaderExterior wire broadcastHeader → Fin (R₁+1) → Bank w₁}
    {mem : HeaderExterior wire broadcastHeader → Fin (R₁+1) → Memory w₁}
    {pp lp : ℕ → ℕ × ℕ} {representative : ℕ → Fin (R₁+1)}
    {group : Fin (planner₁).cube.header.d → Fin (R₁+1)} {initialBase receiving : ℕ}
    {pinSites : Fin (R₁+1) → Pins.Layout}
    {inputFields : HeaderExterior wire broadcastHeader → (u : Fin (R₁+1)) → Pins.ProcessorFields (pinSites u)}
    {broadcastFrame : Fin (R₁+1) → BroadcastFrame} {guess : Fin (R₁+1) → ℕ → Bool}
    {I : Type u} [Fintype I] {resides : I → Fin (planner₁).cube.cells} {keyID : I ↪ ℕ} {sizes : I → ℕ}
    (fixed : Block (R₁+1)) (raw : CheckedBroadcast (planner₁).cube) (site : _) (frame : _),
    let target := cal.frozenReportTest grid qpos position chart reader chargeFit values hist
      (X:=X) (L:=wire) (broadcastHeader:=broadcastHeader) (pin:=pin) (pub:=pub) (mac:=mac)
      (reg:=reg) (mem:=mem) (pp:=pp) (lp:=lp) (representative:=representative) (group:=group)
      (initialBase:=initialBase) (receiving:=receiving) (pinSites:=pinSites) (inputFields:=inputFields)
      (broadcastFrame:=broadcastFrame) (guess:=guess) (I:=I) (resides:=resides) (keyID:=keyID) (sizes:=sizes)
      fixed raw.val site frame .publication
    (∀ z u, let s := site z u
      let base := (pub z u 0).val
      s.old=routingExtension ((planner₁).extension nativePin (broadcastFrame u).team w₁ (signedBudgetWords w₁ outside₁))
        dir₁ origin₁ (planner₁).cube.cables (planner₁).cube.cells ∧
      s.control=controlsAt ∧ (planner₁).OpenRoom base (tabs).ends controlsAt (tabs).livePairs
        ((dir₁).teams*(dir₁).sites) (dir₁).entries (2^rankDepth) w₁ ∧
      (privateLayout base origin₁ (planner₁).cube.cables (planner₁).cube.cells (dir₁).entries (dir₁).description
        (selectedTask).p.privateGap).Image (readings s.geometry) (dir₁).entries (readings s.middle) ∧
      base+112≤receiving ∧ receiving+7*(dir₁).candidates≤origin₁) →
    (∀ z u, cal.IssuedPrivateFields grid qpos position chart reader chargeFit values hist (readings (site z u).geometry)) →
    target

set_option maxRecDepth 15000 in
set_option maxHeartbeats 500000 in
/-- The emitted private words and the acquired site placements give the
complete original report publication on every selected processor. -/
theorem SignedCalendarAt.frozenSiteReportPublication.{u} :
    SignedCalendarAt.SiteReportPublicationAt.{u} cal grid qpos position chart reader chargeFit := by
  intro values hist X wire broadcastHeader pin pub mac reg mem pp lp representative group
    initialBase receiving pinSites inputFields broadcastFrame guess I instI resides keyID sizes fixed raw site frame
    target placed read
  refine fun z => ?_
  have words (u : Fin (R₁+1)) := (cal.numberedPrivateFieldReadback grid qpos position chart reader chargeFit
    values hist (site z u).geometry (read z u)).down
  exact ⟨{ old := fun _ => signedBudgetWords w₁ outside₁
           pin := nativePin
           subtotal := w₁
           literal := fun u => (placed z u).1
           address := fun u => (placed z u).2.1
           space := fun u => (placed z u).2.2.1
           image := fun u => (words u).1
           place := fun u => (placed z u).2.2.2.1
           low := fun u => (placed z u).2.2.2.2.1
           reserve := fun u => (placed z u).2.2.2.2.2
           rest := fun _ => Frame.initial (fun _ => Sum.inr false)
           words := fun u => (words u).2 }⟩

end Diagonal

end BorderVNP
end Computability
end OAI
