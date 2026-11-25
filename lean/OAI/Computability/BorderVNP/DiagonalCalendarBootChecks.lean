import OAI.Computability.BorderVNP.DiagonalCalendarSourceRoom
import OAI.Computability.BorderVNP.DiagonalDeployedFrozenColumns

/-! # Signed packet modes and boot clock on the frozen calendar deployment -/

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

attribute [local irreducible] UniversalMachine.programPrefix Nat.clog

set_option maxRecDepth 7000
set_option maxHeartbeats 1900000

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
local notation3 (prettyPrint := false) "task₁" => b.frozenSignedTask cube (l+1) l (size₁) header (initial₁)
  (dir₁) cap₁ ceiling₁ (located₁).outputs (w₁) (located₁).directories


local notation3 (prettyPrint := false) "eval₁" => signedBody (cube.cubeID paid)
local notation3 (prettyPrint := false) "lib₁" => siteLibrary SparseExterior.driver
local notation3 (prettyPrint := false) "mark₁" => fun _ : Fin 8 => some false
local notation3 (prettyPrint := false) "P₁" => (signedProgram (cube.cubeID paid)).program

/-- Both reference-packet modes, the installed clock, and rejection of
malformed exteriors hold at every operand address of this chosen scale. -/
theorem SignedCalendarAt.frozenPacketPlacements
    (valuation entry totals : Fin (R₁+1) → ℕ) (extension : Fin (R₁+1) → Fin 81 → Word (w₁)) :
    let pack := fun u => reader.packetAt
      (ReaderPlacement.inArena initial₁ (valuation u) (entry u) (totals u) (extension u))
    AllocatedPacketModes eval₁ lib₁ mark₁ geo₁ (layout₁).header reader.packetBitCount pack ∧
    AllocatedPacketReady eval₁ lib₁ mark₁ geo₁ (layout₁).header reader.packetBitCount pack ∧
    AllocatedPacketRejects eval₁ lib₁ mark₁ geo₁ (layout₁).header reader.packetBitCount pack := by
  let L := layout₁
  have linkEq : b.physical.link (l+1) = ℓ₁ := by
    have sizes := b.sizes (Nat.succ_pos l)
    rw [sizes.1]
    exact sizes.2.1
  let carried : Routing.WireLayout (R₁+1) (r₁) (b.physical.link (l+1)) :=
    ⟨L.three,L.width,L.header,fun edge => by rw [linkEq]; exact L.fits edge⟩
  exact cal.sites.choose_spec chart reader chargeFit carried (cal.frozenLayout_fields chart reader chargeFit).2.1
    valuation entry totals extension

/-- The actual installed packet startup is metered on the calendar's own
scale and header, for every subsequent literal and choice of addresses. -/
theorem SignedCalendarAt.frozenBootMeter :
    reader.FrozenBootMeter cube (geo₁) (layout₁) := by
  intro valuation entry totals ext site u
  exact (cal.frozenPacketPlacements chart reader chargeFit valuation entry totals ext).2.1.installedTicks site u

/-- A named physical edge on this attained layout. -/
def SignedCalendarAt.frozenRouteBlock : Routing.Block (R₁+1) :=
  let h := (layout₁).three
  ⟨(⟨0,by omega⟩,⟨1,by omega⟩),Nat.zero_lt_one⟩

local notation3 (prettyPrint := false) "selectedTask" => cal.frozenTask grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "selectedSites" => cal.frozenSites grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "table₁" => (located₁).raw.reserve ceiling₁
local notation "outside₁" => TeamScales.exterior (ξ₁) (r₁) (l+1)
local notation3 (prettyPrint := false) "directory₁" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "fresh₁" => (initial₁).next+7*(directory₁).candidates
local notation3 (prettyPrint := false) "origin₁" =>
  Allocation.dest fresh₁ cap₁ (table₁).size (located₁).outputs w₁
local notation3 (prettyPrint := false) "route₁" => routingExtension (signedBudgetWords w₁ outside₁)
  directory₁ origin₁ (selectedTask).cube.cables (selectedTask).cube.cells
local notation3 (prettyPrint := false) "placed₁" u => reader.frozenTaskPlacement selectedTask initial₁ u route₁
local notation3 (prettyPrint := false) "pin₁" u => CubeHeaderInstall.pinFields (placed₁ u).extension
  (Allocation.stop fresh₁ cap₁ (table₁).size (located₁).outputs w₁ w₁) (selectedTask).cube.header.d
  ((selectedTask).cube.n+1) ((selectedTask).cube.h*(selectedTask).cube.b) (selectedTask).cube.header.blocks cap₁
  (BorderVNP.Cube.Physical.declarationCap (selectedTask).cube.n (selectedTask).cube.header.d
    (selectedTask).cube.header.blocks (selectedTask).cube.b (selectedTask).cube.h (selectedTask).cube.s)
local notation3 (prettyPrint := false) "stripe₁" => GeometryAdviceRate.stripeWidth
  (GeometryOutput.packetCount cap₁ (table₁).size (located₁).outputs w₁*w₁) r₁
local notation3 (prettyPrint := false) "fields₁" u => Allocation.fields (pin₁ u) fresh₁ cap₁ (table₁).size
  (located₁).outputs w₁ ((initial₁).literal/4) stripe₁
local notation3 (prettyPrint := false) "packet₁" u => reader.packetAt (ReaderPlacement.inArena initial₁
  (placed₁ u).valuation (placed₁ u).entry (placed₁ u).totals (fields₁ u))

/-- The three signed packet checks on the actual valuation, entry, total,
pin and complete gate-stripe fields of the frozen site table. -/
theorem SignedCalendarAt.frozenPacketChecks :
    let pack := fun u : Fin (R₁+1) => packet₁ u
    AllocatedPacketModes eval₁ lib₁ mark₁ geo₁ (layout₁).header reader.packetBitCount pack ∧
    AllocatedPacketReady eval₁ lib₁ mark₁ geo₁ (layout₁).header reader.packetBitCount pack ∧
    AllocatedPacketRejects eval₁ lib₁ mark₁ geo₁ (layout₁).header reader.packetBitCount pack :=
  cal.frozenPacketPlacements chart reader chargeFit (fun u => (placed₁ u).valuation) (fun u => (placed₁ u).entry)
    (fun u => (placed₁ u).totals) (fun u => fields₁ u)

/-- Every actual positive or rejecting site starts within its allotted
number of ticks, on the exact deployed literal and native pin frame. -/
theorem SignedCalendarAt.frozenPacketClock :
    let wire := wiringWith prog₁ P₁ selectedSites pins₁ ℓ₁ (l+1) ec₁ (geo₁).fits
    ∀ u : Fin (R₁+1), let ad := (initial₁).unitAddresses (adviceOffsetWith prog₁ r₁ 32 64 w₁ (l+1)) (packet₁ u)
      packetUnitBudget ad.advice.count w₁ (wire.transferFrame u ad.header ad.dst)
        (wire.pinLayout u ad.ibase ad.hbase ad.starbase) ≤ TeamScales.ticks ξ₁ r₁ (l+1) := by
  intro wire u
  exact cal.frozenBootMeter chart reader chargeFit (fun v => (placed₁ v).valuation) (fun v => (placed₁ v).entry)
    (fun v => (placed₁ v).totals) (fun v => fields₁ v) selectedSites u

/-- The native reader's own three allocated word banks and full signed
profile extension satisfy the selected clock on the same deployed sites. -/
theorem SignedCalendarAt.frozenNativePacketClock :
    let task := selectedTask
    let wire := wiringWith prog₁ P₁ selectedSites pins₁ ℓ₁ (l+1) ec₁ (geo₁).fits
    let raw := SignedTaskArena.rawAddress initial₁ task.cube.header.profile task.cube.n
      task.cube.header.d task.cube.header.cap
    let ext := fun u : Fin (R₁+1) => signedProfileExtension task (signedBudgetWords w₁ outside₁) directory₁
      origin₁ task.cube.cables task.cube.cells raw u.val w₁ fresh₁ cap₁ (table₁).size (located₁).outputs
      w₁ ((initial₁).literal/4) stripe₁
    let par := pairedTableParameters (l+1) (size₁)
    let nodes := Fintype.card (Board.Physical par (budget₁+6) w₁ (paid.Entry ⊕
      _root_.OAI.Computability.BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width))
    let guesses := Fintype.card (Guess (Fin par) reader.gridRank (Nat.clog 2 common.p+1) (Nat.clog 2 common.p))
    ∀ u : Fin (R₁+1),
      let ref := reader.nativePacket (task.valuation w₁) (task.entry w₁ nodes guesses reader.gates)
        (initial₁).ibase (initial₁).hbase task.tallyBits (ext u)
      let ad := (initial₁).unitAddresses (adviceOffsetWith prog₁ r₁ 32 64 w₁ (l+1)) ref
      packetUnitBudget ad.advice.count w₁ (wire.transferFrame u ad.header ad.dst)
        (wire.pinLayout u ad.ibase ad.hbase ad.starbase) ≤ TeamScales.ticks ξ₁ r₁ (l+1) := by
  intro task wire raw ext par nodes guesses u
  exact cal.frozenBootMeter chart reader chargeFit (fun _ => task.valuation w₁)
    (fun _ => task.entry w₁ nodes guesses reader.gates) (fun _ => task.tallyBits) ext selectedSites u

private theorem startupBelowGeometry {next rows profile gates outputs field width : ℕ}
    (fit : Allocation.stop (next+7*rows) profile gates outputs field width < 2^width) : next < 2^width := by
  unfold Allocation.stop Allocation.packed Allocation.dense Allocation.dest Allocation.temp at fit
  omega

/-- Numerical hypotheses for the deployed issued executor and its decoder, on
their actual descriptor directory, geometry stripe, startup arena and header. -/
theorem SignedCalendarAt.frozenBootBounds :
    let first := freeStartWith prog₁ r₁ 32 64 w₁ (l+1)
    let stripe := Allocation.stripe fresh₁ cap₁ (table₁).size (located₁).outputs w₁ ((initial₁).literal/4) stripe₁
    JointRoom directory₁ first a₁ (signedBootStripe first) stripe ∧
      reader.packetBitCount ≤ r₁ ∧ (initial₁).next < 2^w₁ ∧ 0<w₁ ∧ 2<R₁+1 ∧ 0<(layout₁).header ∧
      (layout₁).header≤r₁*ℓ₁ ∧ Allocation.stop fresh₁ cap₁ (table₁).size (located₁).outputs w₁ w₁ < 2^w₁ := by
  have fits := cal.frozenSourceRoom grid qpos position chart reader chargeFit
  have capped : (layout₁).header≤r₁*ℓ₁ := by
    have h := (layout₁).fits (cal.frozenRouteBlock chart reader chargeFit)
    omega
  exact ⟨fits.2.2.2.1,fits.2.1,startupBelowGeometry fits.2.2.2.2.1,
    grid.word_eq.symm ▸ Nat.pow_pos grid.log_pos,(layout₁).three,fits.2.2.1,capped,fits.2.2.2.2.1⟩

/-- The unit clock written with exactly the enriched wire used by the issued
executor, at its real team-specific header, destination and private pin spans. -/
theorem SignedCalendarAt.frozenSewnPacketClock :
    let wire := CellEntries.SewnTape.wiring (regs:=64) (w:=w₁) (ec:=ec₁) (width:=w₁+1) prog₁ (geo₁).fits
      ((selectedSites).enrichedFree prog₁ P₁ (l+1) ec₁ ℓ₁) pins₁
    ∀ u : Fin (R₁+1), let ad := (initial₁).unitAddresses (adviceOffsetWith prog₁ r₁ 32 64 w₁ (l+1)) (packet₁ u)
      packetUnitBudget ad.advice.count w₁ (wire.transferFrame u ad.header ad.dst)
        (wire.pinLayout u ad.ibase ad.hbase ad.starbase) ≤ TeamScales.ticks ξ₁ r₁ (l+1) := by
  have met := cal.frozenPacketClock grid qpos position chart reader chargeFit
  rw [wiringWith_enriched] at met
  exact met

end Diagonal

end BorderVNP
end Computability
end OAI
