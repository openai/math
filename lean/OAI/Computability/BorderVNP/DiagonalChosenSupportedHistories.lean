import OAI.Computability.BorderVNP.PackedHistoryFrozenPositiveSites
import OAI.Computability.BorderVNP.DiagonalParsedProfileReturn
import OAI.Computability.BorderVNP.DiagonalBootedRouteDecoding

/-! # The actual reserved profile and pins of every clocked joint preparation -/

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
variable {teams r multBits tally W pinWidth pc routines a link n e : ℕ}
local notation "indexWidth" => (pairedTableParameters (k+1) s+2)*pinWidth
variable (reader : ChosenReader chart (teams+1) r multBits tally W pinWidth)
variable (physical : UniversalMachine.Program) (P : TeamOpcode.Program pc 64 32 routines)
variable (S : SiteData teams r 64 32 W a) (fit : fitsWith physical 64 32 r W a teams link n e)
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
local notation "arena" => reader.startupArenaWith (n:=n) (reg:=64) physical a link L.header
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
local notation "start" => freeStartWith physical r 32 64 W n
local notation "sites" => reader.startupSitesWith physical P S place fit D boot st bootBits geometryBits strings L.header
variable {axes groups cap columns box lanes selectors symbols : ℕ}
variable (gen : CellMacro.Generator.Fragment CellMacro.Generator.IO)
    (id : Cube.TableEntry axes box lanes selectors symbols → ℕ)

open Routing Cube.Physical CellMacro.Generator RoutingISA.CompactMachine

set_option maxRecDepth 7500
set_option maxHeartbeats 2400000

/-- Decode the supported positive branch of the chosen reader. Every returned
profile is a true shortened geometry history because the machine ran the same
augmented, reserved table on this very shared exterior. Pins, claims and routes
are restored on the individual teams' original registers and memories. -/
noncomputable def ChosenReader.frozenSupportedPreparations (gateFit : (geometryTable history slots fits emit x).size ≤ gateCeiling)
    (headerWidth : L.header = JointHeader.PositiveFields.width reserve axes groups cap (teams+1) columns tally)
    (pin : Fin indexWidth → Bool) (regions : JointRoom D start a boot st) (copiesFit : reader.packetBitCount ≤ r)
    (width : b ≤ W) (endFits : Allocation.stop fresh reserve gateCeiling o b W < 2^W)
    (args : Fin (teams+1) → UnitAddresses) (fixed : Block (teams+1)) (hw : 0<W)
    (size : ∀ u, (args u).header=L.header) (base : Fin (teams+1) → ℕ) :
    let T := sites
    let G := wiringWith physical P T indexWidth link n e fit
    let code := (nativeCode).toEmbedding.trans (Function.Embedding.subtype _)
    ∀ (fr : ∀ u, (G.transferFrame u (args u).header (args u).dst).Fits W (base u))
      (B : (y : {ext // PositiveExterior G args pin W ext}) → (u : Fin (teams+1)) →
        BootedPinStart gen G T.publicWords T.registers args pin y.val u),
      BootedPinStart.PreparedHistoryDecoder gen id G T.publicWords T.registers pin L headerWidth code args fixed hw
        size base fr B := by
  intro T G code fr B
  apply BootedPinStart.decodePreparedHistory
  intro p wire u node prep
  let native := TeamSiteEvents.macros (w := W) (siteLibrary gen) (nativeClock n)
  have read := reader.frozen_profile_positive_sites physical P S fit valuation entry totals old L plan G₀ tileOrder
    position witness tag siteID edgeID portID tableData x wr hm widths order fits emit D gateCeiling boot bootBits strings
    p gateFit (p.bits_length.trans headerWidth.symm) wire u pin native (T.registers u) regions copiesFit width endFits
  exact (read.1.mp (node.profileOfPrefix prep)).exists

end Diagonal

end BorderVNP
end Computability
end OAI
