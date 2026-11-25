import OAI.Computability.BorderVNP.PackedHistoryFrozenPositiveSites
import OAI.Computability.BorderVNP.PackedHistoryRoutingFrame

/-! # Returning choices and native packet memory on an encoded frozen history -/

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

/-- The ordinary startup operand layout is the very one used by the packet
allocator. Transporting the layout also transports the pin-memory assertion
for the same returned path. -/
private theorem allocatedPaths {w d k time dest count : ℕ}
    (a : StartupArena) (u : Fin a.teams) (slot : ℕ) (p : ReferencePacket w d)
    (op : PacketOperands) (same : op = a.operands u slot p) (F : Pins.ProcessorFields op.layout)
    (f : BroadcastFrame) (hdr : List Bool) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (bank : Bank w) (mem : Memory w) (words : Fin count → ℕ)
    (paths : ProfilePaths (Evaluator.withStartup pinGeometry) k pub mac bank mem True time dest words
      (fun guess after => ∃ trace z saved, Runs pub mac JointHeader.bootHeader bank mem trace z saved ∧
        JointHeader.BootHeaderState F f op.advice p pub hdr z saved ∧
        ∀ j < a.next, after j = Pins.preparedMemory op.layout (Pins.extendGuess guess) saved op.layout.count j)) :
    ∃ fields : Pins.ProcessorFields (a.operands u slot p).layout,
      HEq fields F ∧ ProfilePaths (Evaluator.withStartup pinGeometry) k pub mac bank mem True time dest words
        (BootResidence (F := fields) a u slot p f op.advice pub mac hdr mem bank) := by
  subst op
  exact ⟨F,HEq.rfl,paths⟩

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

set_option maxRecDepth 7000 in
set_option maxHeartbeats 2800000 in
/-- For an encoded original history the signed geometry prefix returns on
every private pin choice. Its actual emitted words and resident boot memory
are available together at the same return, in the chosen packet allocator. -/
theorem ChosenReader.frozen_profile_chosen_paths_physical
    (gateFit : (geometryTable history slots fits emit x).size ≤ gateCeiling) (length : (hdr).length = L.header)
    (wire : HeaderExterior L hdr) (u : Fin (teams+1))
    (pin : Fin indexWidth → Bool) (mac : TeamOpcode.Macros W 8) (bank : Bank W)
    (regions : JointRoom D start a boot st) (copiesFit : reader.packetBitCount ≤ r) (width : b ≤ W)
    (endFits : Allocation.stop fresh reserve gateCeiling o b W < 2^W)
    (hist : (packHistory leaf plan.compiled.machine.epoch rounds).Index) (writes : (nativeCode hist).val = word) :
    let T := sites
    let B := reader.siteOperandsWith physical P S place fit L.header u
    let refPacket := reader.packetAt (place u)
    let pub := T.publicWords u
    let G := wiringWith physical P T indexWidth link n e fit
    let F := G.processorFields u pin wire.val B.layout.ibase B.layout.hbase B.layout.starbase
    let f := G.transferFrame u L.header B.broadcastBase
    let initial := RAMMemory.initialMemory F.header.length (TeamTapeInputEmit.headerWord W F.header)
    let time := jointBudget refPacket.bits.length W+f.readTicks+2+((pinSetup.slots+17*B.layout.count+1)+
      GeometryAdviceRate.ticks gateCeiling reserve o b W)
    let dest := Allocation.dest fresh reserve gateCeiling o b
    let slot := adviceOffsetWith physical r 32 reg W n
    ∃ fields : Pins.ProcessorFields ((arena).operands u slot refPacket).layout,
      HEq fields F ∧ ProfilePaths (Evaluator.withStartup pinGeometry) B.layout.guessWidth pub mac bank initial True time dest
        (emittedWords history slots fits emit x (nativeCode hist).val)
        (BootResidence (F := fields) arena u slot refPacket f B.advice pub mac hdr initial bank) := by
  intro T B refPacket pub G F f initial time dest slot
  have original := reader.siteOperands_arenaWith physical P S fit valuation entry totals extWords L u
  obtain ⟨paths,eff⟩ := (reader.frozen_profile_positive_sites physical P S fit valuation entry totals old L plan
    G₀ tileOrder position witness tag siteID edgeID portID tableData x wr hm widths order fits emit D gateCeiling
    boot bootBits strings physicalHeader gateFit length wire u pin mac bank regions copiesFit width endFits).2 hist writes
  apply allocatedPaths arena u slot refPacket B original F f hdr pub mac bank initial
  constructor
  · exact iff_true_intro ⟨paths (fun _ => false)⟩
  · intro _
    refine ⟨paths,fun g => ⟨(eff g).1,(eff g).2.1,(eff g).2.2.1,fun i => ?_⟩⟩
    have read := plan.compiled.machine.projected_emittedWords leaf bottom x rfl widths order fits aug source emit
      (q := hist) rfl i
    rw [writes] at read
    rw [writes]
    exact ((eff g).2.2.2.2.2.2 i).trans read.symm
  · intro z g same
    obtain ⟨v,rfl⟩ := paths.surjective z
    obtain rfl : v=g := List.ofFn_injective ((eff v).1.symm.trans same)
    exact (eff v).2.2.2.1

set_option maxRecDepth 7000 in
set_option maxHeartbeats 2800000 in
/-- Enumerate the native returns of the encoded history in the allocated pin layout. -/
theorem ChosenReader.frozen_profile_chosen_paths
    (gateFit : (geometryTable history slots fits emit x).size ≤ gateCeiling) (length : (hdr).length = L.header)
    (wire : HeaderExterior L hdr) (u : Fin (teams+1))
    (pin : Fin indexWidth → Bool) (mac : TeamOpcode.Macros W 8) (bank : Bank W)
    (regions : JointRoom D start a boot st) (copiesFit : reader.packetBitCount ≤ r) (width : b ≤ W)
    (endFits : Allocation.stop fresh reserve gateCeiling o b W < 2^W)
    (hist : (packHistory leaf plan.compiled.machine.epoch rounds).Index) (writes : (nativeCode hist).val = word) :
    let T := sites
    let B := reader.siteOperandsWith physical P S place fit L.header u
    let refPacket := reader.packetAt (place u)
    let pub := T.publicWords u
    let G := wiringWith physical P T indexWidth link n e fit
    let F := G.processorFields u pin wire.val B.layout.ibase B.layout.hbase B.layout.starbase
    let f := G.transferFrame u L.header B.broadcastBase
    let initial := RAMMemory.initialMemory F.header.length (TeamTapeInputEmit.headerWord W F.header)
    let time := jointBudget refPacket.bits.length W+f.readTicks+2+((pinSetup.slots+17*B.layout.count+1)+
      GeometryAdviceRate.ticks gateCeiling reserve o b W)
    let dest := Allocation.dest fresh reserve gateCeiling o b
    let slot := adviceOffsetWith physical r 32 reg W n
    ∃ fields : Pins.ProcessorFields ((arena).operands u slot refPacket).layout,
      ProfilePaths (Evaluator.withStartup pinGeometry) B.layout.guessWidth pub mac bank initial True time dest
        (emittedWords history slots fits emit x (nativeCode hist).val)
        (BootResidence (F := fields) arena u slot refPacket f B.advice pub mac hdr initial bank) := by
  obtain ⟨fields,_,paths⟩ := reader.frozen_profile_chosen_paths_physical physical P S fit valuation entry totals old L plan
    G₀ tileOrder position witness tag siteID edgeID portID tableData x wr hm widths order fits emit D gateCeiling
    boot bootBits strings physicalHeader gateFit length wire u pin mac bank regions copiesFit width endFits hist writes
  exact ⟨fields,paths⟩

end Diagonal

end BorderVNP
end Computability
end OAI
