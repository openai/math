import OAI.Computability.VPVNP.PairSimulationNominationData
import OAI.Computability.VPVNP.LiveVirtualPairs

/-! # The actual virtual pair witness as descriptor, arc and DFS streams -/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorBounds LabelEvaluator BurstRAM BurstRAM.PrivateRAM
open PairSimulation PairSimulation.LocalHistory NetworkKernel LiveProgram CutSchedule ExponentTrace
open private scanInput from OAI.Computability.VPVNP.PairSimulationScanTrace

universe v
variable {K : Type v} [Field K] {S : BlockSchedule K} {D : FixedProgramDiagonal.Program}
    {B : S.Templates} {n C : ℕ} {hn : 2 ≤ n} {p : Nat.Primes}
    {M : Model p (B.compressorDegree n) (B.compressorEquations hn C)}
    (data : D.ScalarData B hn M)
    (processorFit : ProcessorInput.Fits D.literal n (D.geometry n).d (D.geometry n).H (D.geometry n).w)
    {u : PairExponents B.growthConstant} (V : D.VirtualPairs B u hn C)
    [NeZero (virtualBits D.addressFactor n)]
    (ξ : Exterior (D.chainHeight n) (n^D.constants.deltaPower)) (i : D.groupIndices n) (μ : D.pairNom n C)

attribute [local irreducible] NominationClock

/-- Initial padded cursor-network state for the virtual RAM scan, with its reserved lane
labeling and wire widths determined by the virtual bucket and RAM word sizes. -/
noncomputable abbrev VirtualPairs.scanState := scanInput (laneLabels _ _ V.lanes) V.dimension S (roundedUp 1 4 n) (CursorBounds.wordBits D.addressFactor n)
/-- Compression execution on the virtual cursor state using the fixed model's label values and
the chosen number of schedule blocks. -/
noncomputable abbrev VirtualPairs.selection := B.execute (B.compressorValues hn M) (B.compressorValues_solution hn M) (blockCount (u.θ : ℝ) n) le_rfl (V.scanState)

variable (t : ℕ) (clock : NominationClock (d := virtualBits D.addressFactor n) (e := roundedUp 1 4 n) (Q := V.layout i) (V.data data.advice ξ i μ) V.cap.tags V.cap.capFits t)
    {pp rr kk : ℕ} (N : Machine (CursorBounds.wordBits D.addressFactor n) pp rr kk) (pc : Fin 10 → Fin pp) (reg : Fin 2 ↪ Fin rr)
    (base : Fin kk) (done : Fin pp) (hl : FinalBits.Linked N pc reg base done) (he : N.entry=pc 0)
    (low : ℕ) (pub : N.publicData base=FinalBits.cursor (CursorBounds.wordBits D.addressFactor n) low 0) (extra : ℕ)
    (memory : (V.selection (M := M)).Choices → Memory (CursorBounds.wordBits D.addressFactor n))
    (fit : ∀ z, low+((V.selection (M := M)).finalState z).totalWidth < 2^(CursorBounds.wordBits D.addressFactor n))
    (inputs : WorkerInputs (V.selection (M := M))
      (CompressorRecords.executeOrigins B (B.compressorValues hn M) (B.compressorValues_solution hn M) (blockCount (u.θ : ℝ) n) le_rfl (V.scanState))
      (CursorBounds.wordBits D.addressFactor n))

/-- All streams refer to the actual grammar coefficient machine and its
exact private fuel, reset state and initialized nomination header. -/
noncomputable abbrev VirtualPairs.phaseTrace : TraceEncoding ((V.pairData data processorFit).Path ξ i μ) :=
  nominationTrace (d := virtualBits D.addressFactor n) (e := roundedUp 1 4 n) (Q := V.layout i)
    (V.data data.advice ξ i μ) V.cap.tags V.cap.capFits (laneLabels _ _ V.lanes) V.dimension t clock
    B (B.compressorValues hn M) (B.compressorValues_solution hn M) (blockCount (u.θ : ℝ) n) le_rfl
    N pc reg base done hl he low pub extra memory fit

/-- Replace the semantic selector codes of the virtual occurrence by the corresponding worker
tapes for each motif while retaining its arc and vertex choices. -/
noncomputable abbrev VirtualPairs.phaseEmission :
    SelectorReindex (V.phaseTrace data processorFit ξ i μ t clock N pc reg base done hl he low pub extra memory fit) :=
  nominationReindex (d := virtualBits D.addressFactor n) (e := roundedUp 1 4 n) (Q := V.layout i)
    (V.data data.advice ξ i μ) V.cap.tags V.cap.capFits (laneLabels _ _ V.lanes) V.dimension t clock
    B (B.compressorValues hn M) (B.compressorValues_solution hn M) (blockCount (u.θ : ℝ) n) le_rfl
    N pc reg base done hl he low pub extra memory fit inputs

/-- The chosen virtual branch determines both the terminal graph and the
specific entry memory used by its physical final-arc scan. -/
noncomputable abbrev VirtualPairs.finalData (z : (V.selection (M := M)).Choices) :=
  NominationData (d := virtualBits D.addressFactor n) (e := roundedUp 1 4 n) (Q := V.layout i)
    (V.data data.advice ξ i μ) V.cap.tags V.cap.capFits (laneLabels _ _ V.lanes) V.dimension t clock
    B (B.compressorValues hn M) (B.compressorValues_solution hn M) (blockCount (u.θ : ℝ) n) le_rfl
    N pc reg base done hl he low pub extra memory fit z

/-- The descriptor branch and all terminal choices classify the same
monomial occurrence as the canonical `VirtualPairs.witness`. -/
noncomputable def VirtualPairs.phaseDataEquiv :
    ((z : (V.selection (M := M)).Choices) × V.finalData data ξ i μ t clock N pc reg base done hl he low pub extra memory fit z) ≃
      Set.range (V.phaseEmission data processorFit ξ i μ t clock N pc reg base done hl he low pub extra memory fit inputs).emit :=
  nominationDataEquiv (d := virtualBits D.addressFactor n) (e := roundedUp 1 4 n) (Q := V.layout i)
    (V.data data.advice ξ i μ) V.cap.tags V.cap.capFits (laneLabels _ _ V.lanes) V.dimension t clock
    B (B.compressorValues hn M) (B.compressorValues_solution hn M) (blockCount (u.θ : ℝ) n) le_rfl
    N pc reg base done hl he low pub extra memory fit inputs

/-- Decode an actual descriptor and final-vertex datum to its precise
algebraic occurrence in the fixed model. -/
noncomputable def VirtualPairs.choiceDataEquiv :
    ((z : (V.selection (M := M)).Choices) × V.finalData data ξ i μ t clock N pc reg base done hl he low pub extra memory fit z) ≃
      (V.pairData data processorFit).Path ξ i μ :=
  (V.phaseDataEquiv data processorFit ξ i μ t clock N pc reg base done hl he low pub extra memory fit inputs).trans
    (V.phaseEmission data processorFit ξ i μ t clock N pc reg base done hl he low pub extra memory fit inputs).decode

set_option maxHeartbeats 1500000 in
/-- The chosen ordinal tapes, shared-arc calls and site jobs are those of
the same decoded `V.pairData` occurrence. Their increment sums equal its
canonical compressor histogram in every coordinate. -/
theorem VirtualPairs.choiceData_jobs (z : (V.selection (M := M)).Choices)
    (x : V.finalData data ξ i μ t clock N pc reg base done hl he low pub extra memory fit z) :
    let E := V.selection (M := M)
    let X := V.scanState
    let Y := E.finalState z
    let c := E.termChain (B.records (B.compressorValues hn M) (B.compressorValues_solution hn M) (blockCount (u.θ : ℝ) n) le_rfl X) z
    let r := selectedParsers B (B.compressorValues hn M) (B.compressorValues_solution hn M) (blockCount (u.θ : ℝ) n) le_rfl X z
    let P := nominationSites (V.data data.advice ξ i μ) V.cap.tags V.cap.capFits (laneLabels _ _ V.lanes) V.dimension
      (Nat.add_sub_of_le S.degree_bounds.1) (B.compressorValues hn M) t clock
    let p := V.phaseDataEquiv data processorFit ξ i μ t clock N pc reg base done hl he low pub extra memory fit inputs ⟨z,x⟩
    let q := V.choiceDataEquiv data processorFit ξ i μ t clock N pc reg base done hl he low pub extra memory fit inputs ⟨z,x⟩
    p.val.termCalls = ordinalTapes E (CompressorRecords.executeOrigins B (B.compressorValues hn M) (B.compressorValues_solution hn M) (blockCount (u.θ : ℝ) n) le_rfl X) inputs z ∧ p.val.arcCalls = x.arcs.val ∧
      ∀ (ptr : RowPointers c) (leaves : X.network.Site → ℕ × ℕ),
        let jobs := vertexJobs c r ptr P leaves
        p.val.vertices = List.ofFn (fun j => (x.jobs jobs ((siteOrder Y).entries j)).flatMap VertexJob.bits) ∧
          ∀ l, (V.pairData data processorFit).ν ξ i μ q l = ∑ v, ((x.jobs jobs v).map (fun j => j.increment l)).sum :=
  nominationData_jobs (d := virtualBits D.addressFactor n) (e := roundedUp 1 4 n) (Q := V.layout i)
    (V.data data.advice ξ i μ) V.cap.tags V.cap.capFits (laneLabels _ _ V.lanes) V.dimension t clock
    B (B.compressorValues hn M) (B.compressorValues_solution hn M) (blockCount (u.θ : ℝ) n) le_rfl
    N pc reg base done hl he low pub extra memory fit inputs z x

/-- The terminal site clock is chosen before the nomination and auxiliary
header. Every selected canonical counter then meets its clock bound. -/
theorem eventually_virtualNominationClock (D : FixedProgramDiagonal.Program) (B : S.Templates)
    (u : PairExponents B.growthConstant) (C : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn C)
      [NeZero (virtualBits D.addressFactor n)] (adv : Bits (n^D.constants.advicePower))
      (ξ : Exterior (D.chainHeight n) (n^D.constants.deltaPower)) (i : D.groupIndices n) (μ : D.pairNom n C),
      NominationClock (V.data adv ξ i μ) V.cap.tags V.cap.capFits (n^39) := by
  filter_upwards [eventually_nominationClock] with n all hn V inst adv ξ i μ
  apply all _ _ _ V.cap _ _ _ _ (V.layout i) (V.data adv ξ i μ)
  have h := (V.counts i (PairedChain.headers adv ξ i) μ).privateWork
  change 6*(V.data adv ξ i μ).fuel ≤ n^10 at h
  exact (Nat.le_mul_of_pos_left _ (by decide : 0 < 6)).trans h

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
