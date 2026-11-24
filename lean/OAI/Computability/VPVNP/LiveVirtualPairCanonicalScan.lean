import OAI.Computability.VPVNP.LiveVirtualPairOrdinalData
import OAI.Computability.VPVNP.LiveVirtualPairJobCounters

/-!
# Payload coordinates and vertex counters of a virtual pair

Index the semantic shared-bit choices by a zero-based scan. Its payload
equivalence can be composed with the physical shared-bit worker at the
address computed for a selected descriptor branch. The native readback uses
the actual address. The ordinal emission and each vertex's increments use
the same payload and site witnesses through this reindexing.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorBounds LabelEvaluator BurstRAM BurstRAM.PrivateRAM
open PairSimulation PairSimulation.LocalHistory NetworkKernel LiveProgram CutSchedule ExponentTrace

universe v
variable {K : Type v} [Field K] {S : BlockSchedule K} {D : FixedProgramDiagonal.Program}
    {B : S.Templates} {n C : ℕ} {hn : 2 ≤ n} {p : Nat.Primes}
    {M : Model p (B.compressorDegree n) (B.compressorEquations hn C)}
    (data : D.ScalarData B hn M) {u : PairExponents B.growthConstant} (V : D.VirtualPairs B u hn C)
    [NeZero (virtualBits D.addressFactor n)]
    (ξ : Exterior (D.chainHeight n) (n^D.constants.deltaPower)) (i : D.groupIndices n) (μ : D.pairNom n C)

local notation "width" => CursorBounds.wordBits D.addressFactor n
local notation "κ" => B.compressorValues hn M
local notation "κ_ok" => B.compressorValues_solution hn M
local notation "blocks" => blockCount (u.θ : ℝ) n
local notation "sel" => V.selection (M := M)
local notation "source" => V.scanState

attribute [local irreducible] NominationClock

/-- Data for scanning one nominated virtual pair in a fixed model. It bounds the leaf startup
clock and final wire width and supplies the term workers' inputs for each possible sequence
of selected passes. -/
structure CanonicalScan where
  clock : NominationClock (d := virtualBits D.addressFactor n) (e := roundedUp 1 4 n) (Q := V.layout i)
    (V.data data.advice ξ i μ) V.cap.tags V.cap.capFits (n^39)
  widthFit : ∀ z : (sel).Choices, ((sel).finalState z).totalWidth < 2^width
  /-- Term-worker inputs for the selected compressor execution at its RAM word width, indexed
  recursively by the originating pass and all subsequent choices. -/
  inputs : WorkerInputs sel (CompressorRecords.executeOrigins B κ κ_ok blocks le_rfl source) width

variable {data V ξ i μ} (A : CanonicalScan data V ξ i μ)
variable (processorFit : ProcessorInput.Fits D.literal n (D.geometry n).d (D.geometry n).H (D.geometry n).w)

private abbrev scanWords (w : ℕ) : Fin 1 → BurstRAM.Word w := fun _ => FinalBits.cursor w 0 0
private abbrev scanMachine (w : ℕ) := FinalBits.template.instantiate w (scanWords w)
include A in
private theorem capacity (z : (sel).Choices) : 0+((sel).finalState z).totalWidth < 2^width := by
  simpa only [Nat.zero_add] using A.widthFit z

local notation "machine" => scanMachine width
local notation "linked" => FinalBits.template_linked (scanWords width)
local notation "scanMemory" => (fun _ : (sel).Choices => (fun _ => 0 : Memory width))
local notation "enc" => V.phaseTrace data processorFit ξ i μ (n^39) A.clock machine Fin.castSucc (Function.Embedding.refl _) 0 10 linked rfl 0 rfl 0 scanMemory (capacity A)

/-- Trace encoding of the nominated pair's algebraic occurrences using the final-bit scanner
started at cursor zero in zero memory and the clocked nomination leaf readers. -/
noncomputable abbrev CanonicalScan.encoding := enc
/-- Injectively re-encode a canonical scan's selector phases as native term tapes in motif
order, carrying along the same shared-arc and vertex phases. -/
noncomputable abbrev CanonicalScan.emission : SelectorReindex (A.encoding processorFit) :=
  V.phaseEmission data processorFit ξ i μ (n^39) A.clock machine Fin.castSucc (Function.Embedding.refl _) 0 10 linked rfl
    0 rfl 0 scanMemory (capacity A) A.inputs

/-- Shared-arc scan phase on the terminal network of the selected compression branch, using the
final-bit machine and its zero starting cursor. -/
noncomputable abbrev CanonicalScan.arc (z : (sel).Choices) :=
  stateScanPhase ((sel).finalState z) machine Fin.castSucc (Function.Embedding.refl _) 0 10 linked rfl
    0 rfl (scanMemory z) 0 (capacity A z)

/-- Clocked parsers for the initial cursor-network sites, using the nominated auxiliary
machine, its reset memory and the selected model's label values. -/
noncomputable abbrev CanonicalScan.leafSites := nominationSites (V.data data.advice ξ i μ) V.cap.tags V.cap.capFits
  (laneLabels _ _ V.lanes) V.dimension (Nat.add_sub_of_le S.degree_bounds.1) κ (n^39) A.clock

/-- Chain of compression terms along the chosen execution branch, using the templates' record
data for those passes. -/
noncomputable abbrev selectedChain (z : (sel).Choices) := (sel).termChain (B.records κ κ_ok blocks le_rfl source) z
/-- Final-network site parsers obtained by carrying the nomination leaf parsers through the
chosen chain with that branch's local parsers. -/
noncomputable abbrev CanonicalScan.sites (z : (sel).Choices) :=
  finalParsers (selectedChain z) (selectedParsers B κ κ_ok blocks le_rfl source z) A.leafSites

/-- Bijection between a descriptor branch with its terminal arc and site choices and the
ordinal phase lists emitted by the canonical scan. -/
noncomputable def CanonicalScan.ordinals :
    ((z : (sel).Choices) × TerminalData (A.arc z) (A.sites z)) ≃ Set.range (A.emission processorFit).emit :=
  V.phaseDataEquiv data processorFit ξ i μ (n^39) A.clock machine Fin.castSucc (Function.Embedding.refl _) 0 10 linked rfl
    0 rfl 0 scanMemory (capacity A) A.inputs

/-- For every real per-level pointer assignment, the sum of the selected
preorder jobs at all sites is the exponent of the recovered occurrence. -/
theorem CanonicalScan.jobSums (z : (sel).Choices) (x : TerminalData (A.arc z) (A.sites z))
    (ptr : RowPointers (selectedChain z)) (leaves : (source).network.Site → ℕ × ℕ) :
    let jobs := vertexJobs (selectedChain z) (selectedParsers B κ κ_ok blocks le_rfl source z) ptr A.leafSites leaves
    let q := (A.emission processorFit).decode (A.ordinals processorFit ⟨z,x⟩)
    ∀ l, (V.pairData data processorFit).ν ξ i μ q l = ∑ v, ((x.jobs jobs v).map (fun j => j.increment l)).sum :=
  ((V.choiceData_jobs data processorFit ξ i μ (n^39) A.clock machine Fin.castSucc (Function.Embedding.refl _) 0 10
    linked rfl 0 rfl 0 scanMemory (capacity A) A.inputs z x).2.2 ptr leaves).2

/-- Sum of increments to one model-label counter over the preorder jobs of one terminal site,
using the supplied row pointers and leaf addresses. -/
noncomputable abbrev CanonicalScan.siteTotals (z : (sel).Choices) (x : TerminalData (A.arc z) (A.sites z))
    (ptr : RowPointers (selectedChain z)) (leaves : (source).network.Site → ℕ × ℕ) (v : ((sel).finalState z).network.Site)
    (l : B.Entry) : ℕ :=
  let jobs := vertexJobs (selectedChain z) (selectedParsers B κ κ_ok blocks le_rfl source z) ptr A.leafSites leaves
  ((x.jobs jobs v).map (fun a => a.increment l)).sum

/-- All real site deposits, in the site's physical order, give the precise
canonical counter memory required by the pair source-run certificate. -/
theorem CanonicalScan.flush (z : (sel).Choices) (x : TerminalData (A.arc z) (A.sites z))
    (ptr : RowPointers (selectedChain z)) (leaves : (source).network.Site → ℕ × ℕ)
    {g : ℕ} (counterBase grammar : ℕ) (order : Fin g → B.Entry) (m : Memory width) :
    let jobs := vertexJobs (selectedChain z) (selectedParsers B κ κ_ok blocks le_rfl source z) ptr A.leafSites leaves
    let q := (A.emission processorFit).decode (A.ordinals processorFit ⟨z,x⟩)
    Counters.visit counterBase grammar (fun v j => ((x.jobs jobs v).map (fun a => a.increment (order j))).sum)
      (List.ofFn (siteOrder ((sel).finalState z)).entries) m =
    Counters.visit counterBase grammar (fun (v : B.Entry → ℕ) j => v (order j))
      (V.histograms data processorFit ξ i μ q) m := by
  intro jobs q
  exact V.siteFlushes_eq data processorFit ξ i μ q (siteOrder ((sel).finalState z)).entries
    (fun v l => ((x.jobs jobs v).map (fun a => a.increment l)).sum)
    (fun l => (A.jobSums processorFit z x ptr leaves l).symm) counterBase grammar order m

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
