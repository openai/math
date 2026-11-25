import OAI.Computability.BorderVNP.PackedHistoryFrozenChosenPaths

/-! # Physical selection of one history across arbitrary signed declarations -/

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


set_option maxRecDepth 8000 in
set_option maxHeartbeats 3600000 in
/-- One returning physical site determines the unique frozen history. Every
site on every positive declaration with the same profile then enumerates its
own pin choices and reads the same history's packet, with its own saved boot
fields and initial memory. -/
theorem ChosenReader.frozen_profile_header_selection
    (gateFit : (geometryTable history slots fits emit x).size ≤ gateCeiling) (length : (hdr).length = L.header)
    (regions : JointRoom D start a boot st) (copiesFit : reader.packetBitCount ≤ r) (width : b ≤ W)
    (endFits : Allocation.stop fresh reserve gateCeiling o b W < 2^W)
    (first : HeaderExterior L hdr) (team : Fin (teams+1)) (initialPin : Fin indexWidth → Bool)
    (ops : TeamOpcode.Macros W 8) (registers : Bank W) :
    let T := sites
    let G := wiringWith physical P T indexWidth link n e fit
    let op := reader.siteOperandsWith physical P S place fit L.header team
    let firstFields := G.processorFields team initialPin first.val op.layout.ibase op.layout.hbase op.layout.starbase
    let firstMem := RAMMemory.initialMemory firstFields.header.length (TeamTapeInputEmit.headerWord W firstFields.header)
    Nonempty (Returns (Evaluator.withStartup pinGeometry) (T.publicWords team) ops registers firstMem) ↔
      ∃! hist : (packHistory leaf plan.compiled.machine.epoch rounds).Index,
        (nativeCode hist).val=word ∧
        ∀ (p : JointHeader.PositiveFields reserve axes groups cap (teams+1) claimsDim tally),
          p.profile=word → ∀ (wire : HeaderExterior L p.bits) (u : Fin (teams+1))
            (pin : Fin indexWidth → Bool) (mac : TeamOpcode.Macros W 8) (bank : Bank W),
          let B := reader.siteOperandsWith physical P S place fit L.header u
          let pk := reader.packetAt (place u)
          let pub := T.publicWords u
          let F := G.processorFields u pin wire.val B.layout.ibase B.layout.hbase B.layout.starbase
          let f := G.transferFrame u L.header B.broadcastBase
          let initial := RAMMemory.initialMemory F.header.length (TeamTapeInputEmit.headerWord W F.header)
          let time := jointBudget pk.bits.length W+f.readTicks+2+((pinSetup.slots+17*B.layout.count+1)+
            GeometryAdviceRate.ticks gateCeiling reserve o b W)
          let dest := Allocation.dest fresh reserve gateCeiling o b
          let slot := adviceOffsetWith physical r 32 reg W n
          ∃ fields : Pins.ProcessorFields ((arena).operands u slot pk).layout, HEq fields F ∧
            ProfilePaths (Evaluator.withStartup pinGeometry) B.layout.guessWidth pub mac bank initial True time dest
              (emittedWords history slots fits emit x (nativeCode hist).val)
              (BootResidence (F:=fields) arena u slot pk f B.advice pub mac p.bits initial bank) := by
  intro T G op firstFields firstMem
  constructor
  · intro returned
    have read := reader.frozen_profile_positive_sites physical P S fit valuation entry totals old L plan G₀ tileOrder
      position witness tag siteID edgeID portID tableData x wr hm widths order fits emit D gateCeiling boot bootBits
      strings physicalHeader gateFit length first team initialPin ops registers regions copiesFit width endFits
    obtain ⟨hist,decoded,unique⟩ := read.1.mp returned
    refine ⟨hist,⟨decoded,?_⟩,fun other evidence => unique other evidence.1⟩
    intro p same wire u pin mac bank
    have copied := p.bits_length.trans (physicalHeader.bits_length.symm.trans length)
    exact reader.frozen_profile_chosen_paths_physical physical P S fit valuation entry totals old L plan G₀ tileOrder
      position witness tag siteID edgeID portID tableData x wr hm widths order fits emit D gateCeiling boot bootBits
      strings p gateFit copied wire u pin mac bank regions copiesFit width endFits hist (decoded.trans same.symm)
  · rintro ⟨hist,⟨_,paths⟩,_⟩
    obtain ⟨_,_,observed⟩ := paths physicalHeader rfl first team initialPin ops registers
    exact observed.passes.mpr trivial

end Diagonal

end BorderVNP
end Computability
end OAI
