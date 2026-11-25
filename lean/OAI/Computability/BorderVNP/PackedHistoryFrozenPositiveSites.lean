import OAI.Computability.BorderVNP.PackedHistoryChosenProjectedReserved
import OAI.Computability.BorderVNP.PackedFrozenNativeProjection
import OAI.Computability.BorderVNP.PackedFrozenSeedInputs
import OAI.Computability.BorderVNP.DiagonalPositiveExteriorRoutes
import OAI.Computability.BorderVNP.DiagonalPositiveHeaderClaims

/-! # The complete frozen profile validator on raw positive signed exteriors -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing MvPolynomial ResidueBox ResiduePins ResidueEntryInput DiagonalResidueRAM
open VPVNP BurstRAM RAMTape TeamContraction TeamContraction.ProcessorSlots VerifierNetwork
open RoutingISA RoutingISA.Pins GeometryAdvice GeometryFrameEncoding PackedHistoryCircuit
open Shortening Adaptive Packing Epoch.Round RoutingISA.Evaluator
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter PublicCapacity
open Cover Packing.Inherited Packing.Inherited.FrozenTape PackedHistoryCircuit.Normalized.SelectedSchedule
open ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar BorderVNP.Cube
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {K : Type} [Field K] {dim labels : ℕ} {ι : Type} [Fintype ι]
variable {paid : PaidIdentity K dim labels} {aux : ι → K} {q k s : ℕ}
variable {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))} {R : CommonField paid aux q k s ord}
variable {chart : AdvisedBranch R} [Fact R.p.Prime] [Algebra (ZMod R.p) chart.E]
variable {teams r multBits tally W pinWidth pc reg routines a link n e : ℕ}
local notation "indexWidth" => (pairedTableParameters (k+1) s+2)*pinWidth
variable (reader : ChosenReader chart (teams+1) r multBits tally W pinWidth)
variable (physical : UniversalMachine.Program) (P : TeamOpcode.Program pc reg 32 routines)
variable (S : SiteData teams r reg 32 W a) (fit : fitsWith physical reg 32 r W a teams link n e)
variable (valuation entry totals : Fin (teams+1) → ℕ) (old : Fin (teams+1) → Fin 81 → Word W)
variable (L : Routing.WireLayout (teams+1) r link)
variable [NeZero dim] {sched : Normalized.SiteSchedule paid} {depth rounds copies headerFactor Q : ℕ}
    (plan : SelectedSchedule.SeedPlan sched n r depth rounds copies headerFactor Q)
    {time p₀ seedLink inner : ℕ} {Edge : Type} [Fintype Edge] (G₀ : Wiring teams r time p₀ seedLink inner n Edge)
    (tileOrder : Fin (ExternalSew.GridHosts.tileCount (Fintype.card (Epoch.Cube dim)) depth) ≃
      (Fin (Fintype.card (Epoch.Cube dim)) → Cover.Deck (depth+2)))
    (position : (Fin (Fintype.card (Epoch.Cube dim)) → Cover.Deck (depth+2)) →
      {v : EuclideanSpace ℝ (Fin dim) // ‖v‖ ≤ 1})
    {X : Type} [Fintype X] {g : ℕ} {len : Fin n} {state : Fin g}
    (witness : DeckGrid.WiredWitness G₀ len dim (Fintype.card (Epoch.Cube dim)) depth tileOrder state)
    (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (siteID : (witness.routedFine position).Site ↪ Fin ns) (edgeID : (witness.routedFine position).Edge ↪ Fin ne)
    (portID : Fin r × Fin (publicWidth G₀) ↪ Fin np)
    (tableData : (DeckGrid.seedBundle G₀ (Fintype.card (Epoch.Cube dim)) depth tileOrder position copies).Tables K)
    (x : X → Bool)
    (wr : SelectedSchedule.WidthRanges sched (depth+1) rounds (60*TeamScales.logWidth r n)) (hm : 0<labels)
    {reserve o b : ℕ} (widths : ℕ → ℕ)
    (order : ∀ j, EnrichedOuter.Machine.Guess sched (depth+1) (fun _ _ => 60*TeamScales.logWidth r n) j ≃ Fin (widths j))
    (fits : broadcastWidth (fan sched) widths rounds ≤ reserve)
    (emit : Frame ((X ⊕ Fin reserve) ⊕ ProgramSchemas.outerPins sched (depth+1) (60*TeamScales.logWidth r n)
      (Boundary.seedFormat G₀ tileOrder position copies) rounds) (Fin o × Fin b))

local notation3 (prettyPrint := false) "M" => plan.compiled.machine
local notation3 (prettyPrint := false) "bottom" => (plan.execute G₀ tileOrder position X).choose
local notation3 (prettyPrint := false) "leaf" => plan.frozenLeaf G₀ tileOrder position witness tag siteID edgeID portID tableData x
local notation3 (prettyPrint := false) "source" => plan.frozenStart G₀ tileOrder position X
local notation3 (prettyPrint := false) "fmt" => Boundary.seedFormat G₀ tileOrder position copies
local notation "hdrPorts" => WorkWords.grouped (CoverScale.sites (Epoch.Cube dim) (depth+1))
  (copies*ExternalSew.GridHosts.inputBlockWidth r n (Fintype.card (Epoch.Cube dim)) depth)
local notation "key" => Equiv.toEmbedding (finCongr (SelectedSchedule.seedPortCount (D:=dim) depth))
local notation3 (prettyPrint := false) "aug" => plan.compiled.tapeSteps fmt hdrPorts key wr hm
local notation3 (prettyPrint := false) "history" => PackedHistoryCircuit.compile aug rounds le_rfl (repeatLeaf (fan sched) source rounds)
local notation "slots" => broadcastOrder (fan sched) widths order rounds
local notation3 (prettyPrint := false) "nativeCode" => plan.compiled.machine.nativeCode leaf bottom x rfl widths order fits
variable (D : Packing.Directory.Layout)
local notation "arena" => reader.startupArenaWith (n:=n) (reg:=reg) physical a link L.header
local notation "fresh" => StartupArena.next arena + 7*D.candidates
variable (gateCeiling : ℕ)
local notation "table" => reservedGeometryTable history slots fits emit x gateCeiling
local notation "off" => StartupArena.literal arena/4
local notation "ell" => GeometryAdviceRate.stripeWidth (GeometryOutput.packetCount reserve (Table.size table) o b*W) r
local notation "st" => Allocation.stripe fresh reserve (Table.size table) o b off ell
local notation "extWords" => fun u : Fin (teams+1) => Allocation.fields (old u) fresh reserve (Table.size table) o b off ell
local notation "place" => fun u : Fin (teams+1) =>
  ReaderPlacement.inArena arena (valuation u) (entry u) (totals u) (extWords u)
local notation "geometryBits" => fun _ : Fin (teams+1) => GeometryAdvice.serialized (GeometryAdvice.packet (w := W)
  fresh (Allocation.packed fresh reserve (Table.size table) o b W) table (fun i => StartupArena.broadcastBase arena+1+Fin.val i))
variable (boot : GeometryAdvice.Stripe) (bootBits : Fin (teams+1) → List Bool)
variable (strings : Fin D.entries → Fin D.description → Bool)
local notation "start" => freeStartWith physical r 32 reg W n
local notation "sites" => reader.startupSitesWith physical P S place fit D boot st bootBits geometryBits strings L.header
variable {axes groups cap claimsDim : ℕ} (physicalHeader : JointHeader.PositiveFields reserve axes groups cap (teams+1) claimsDim tally)
local notation "hdr" => JointHeader.PositiveFields.bits physicalHeader
local notation "word" => JointHeader.PositiveFields.profile physicalHeader

set_option maxRecDepth 6500 in
set_option maxHeartbeats 3200000 in
/-- The augmented geometry program accepts precisely the original public history codes,
even on an arbitrary assignment of the other exterior wires. All its physical
pin guesses, retained boot operands and terminal RAM rows belong to the same
history as the one decoded from the common header. -/
theorem ChosenReader.frozen_profile_positive_sites
    (gateFit : (geometryTable history slots fits emit x).size ≤ gateCeiling) (length : (hdr).length = L.header)
    (wire : HeaderExterior L hdr) (u : Fin (teams+1))
    (pin : Fin indexWidth → Bool) (mac : TeamOpcode.Macros W 8) (bank : Bank W)
    (regions : JointRoom D start a boot st) (copiesFit : reader.packetBitCount ≤ r) (width : b ≤ W)
    (endFits : Allocation.stop fresh reserve gateCeiling o b W < 2^W) :
    let T := sites
    let B := reader.siteOperandsWith physical P S place fit L.header u
    let p := reader.packetAt (place u)
    let pub := T.publicWords u
    let G := wiringWith physical P T indexWidth link n e fit
    let exterior := wire.val
    let F := G.processorFields u pin exterior B.layout.ibase B.layout.hbase B.layout.starbase
    let f := G.transferFrame u L.header B.broadcastBase
    let initial := RAMMemory.initialMemory F.header.length (TeamTapeInputEmit.headerWord W F.header)
    let returned := Returns (Evaluator.withStartup pinGeometry) pub mac bank initial
    let time := jointBudget p.bits.length W+f.readTicks+2+((pinSetup.slots+17*B.layout.count+1)+
      GeometryAdviceRate.ticks gateCeiling reserve o b W)
    let dest := Allocation.dest fresh reserve gateCeiling o b
    (Nonempty returned ↔ ∃! q, (nativeCode q).val = word) ∧
    ∀ q, (nativeCode q).val = word → ∃ paths : (Fin B.layout.guessWidth → Bool) ≃ returned, ∀ guess,
      let out := paths guess
      let mem := out.val.2.2
      out.val.1.flatMap TeamRAM.Event.choices = List.ofFn guess ∧ traceCost out.val.1 ≤ time ∧ signedWeight out.val.1 = 1 ∧
      (∃ trace z saved, Runs pub mac JointHeader.bootHeader bank initial trace z saved ∧
        JointHeader.BootHeaderState F f B.advice p pub hdr z saved ∧
        ∀ i < (arena).next, mem i = Pins.preparedMemory B.layout (Pins.extendGuess guess) saved B.layout.count i) ∧
      JointHeader.FlatAt mem f.dst hdr ∧
      (∃ passed, (nativeCode).symm ⟨profileRAM mem f.dst,passed⟩ = q) ∧
      ∀ i, readings mem (dest+i.val) = ParseBatchSort.value (fun j => emit.eval
        (Sum.elim (Sum.elim x word) (output aug rounds le_rfl (repeatLeaf (fan sched) source rounds) x (plan.compiled.machine.packBits leaf rounds le_rfl q))) (i,j)) := by
  intro T B refPacket pub G exterior F f initial returned time dest
  let decl := DeclarationBits.spelling physicalHeader.cube
  let encoded := JointHeader.padded (JointHeader.evaluation (List.ofFn word++decl) tally physicalHeader.rawCounts) 0
  have spelling : hdr = encoded := physicalHeader.bits_eq_emitted
  have encLen : encoded.length = L.header := spelling ▸ length
  have common : ∀ t, (L.exteriorEquiv wire.val).broadcast t = JointHeader.headerBits encoded encLen := by
    intro t
    have h : JointHeader.observed L wire.val t = encoded := (wire.property t).trans spelling
    have he := JointHeader.observed_bits L wire.val t
    have same {l₁ l₂ : List Bool} {h₁ : l₁.length = L.header} {h₂ : l₂.length = L.header} (eqn : l₁=l₂) :
        JointHeader.headerBits l₁ h₁ = JointHeader.headerBits l₂ h₂ := by cases eqn; rfl
    exact he.symm.trans (same h)
  have result := reader.projected_profile_startupReservedCommonWith physical P S fit valuation entry totals old L
    M leaf bottom x rfl widths order fits (fun _ z => .inl (.inl z)) aug
    (plan.compiled.tapeSteps_project fmt hdrPorts key wr hm) source
    (Boundary.seedTapeFrame_geometry sched plan G₀ tileOrder position bottom x) emit D gateCeiling boot bootBits strings
    word decl tally 0 physicalHeader.rawCounts gateFit encLen wire.val common u pin mac bank regions copiesFit width endFits
  exact spelling.symm ▸ result

end Diagonal

end BorderVNP
end Computability
end OAI
