import OAI.Computability.VPVNP.LiveVirtualPairHistograms
import OAI.Computability.VPVNP.LiveCompressedPairOccurrence

/-! # From source tapes and histogram visits to the fixed program's compressed call

A native schedule emits concrete per-call tapes from its selector, arc and final-site
phases. The accepting-tape equivalence below uses the identity on those tapes.
The only counter condition on the simulator concerns its actual writes. Their
mathematical values follow from readback of the canonical virtual occurrence.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group.CompressedPaths

open BurstRAM BurstRAM.PrivateRAM PairSimulation.LocalHistory

/-- Source-level obligations for one schedule on the actual prepared memory.
The returned reports are the unrelocated reports of the pair instruction table. -/
structure SourceRuns (G : Group) (input : Memory G.w) (X : Type) (visited : X → Memory G.w) (S H : ℕ) where
  /-- Trace encoding that identifies the source schedule's semantic occurrences with their
  selector, arc and vertex phases. -/
  encoding : TraceEncoding X
  /-- Injective translation from those encoded phases to native motif-ordinal term bursts and
  the corresponding arc and vertex bursts. -/
  emission : SelectorReindex encoding
  /-- Per-call private tapes for each emitted ordinal phase list. Their range is exactly the
  tapes on which the native pair program runs from the prepared memory to a halt. -/
  tapes : Set.range emission.emit → List (List Bool)
  tapes_injective : Function.Injective tapes
  accepts : ∀ bs, bs ∈ Set.range tapes ↔ ∃ rs, runSegment (native G) (fuel G) (some 0) input bs = some rs ∧
    endState (some 0) rs = none
  tag : PreservesTag G input
  effects : ∀ p rs, runSegment (native G) (fuel G) (some 0) input (tapes p) = some rs →
    (∀ a, Auxiliary.headerBase G ≤ a → a < Auxiliary.tableBase G → after input (eventLog rs) a = input a) ∧
    (∀ a : Fin (labelCount G), after input (eventLog rs) (Auxiliary.counterBase G+a.val) =
      visited (emission.decode p) (Auxiliary.counterBase G+a.val)) ∧
    4*RAMBuckets.cost Report.probes rs ≤ S*H ∧
    ∀ r ∈ rs, r.events.length+4 ≤ fuel G ∧ 3+r.probes ≤ H

variable {G : Group} {input : Memory G.w} {X : Type} {visited : X → Memory G.w} {S H : ℕ}
    (U : SourceRuns G input X visited S H)

/-- The equivalence to raw accepted paths preserves the actual list of tapes. -/
noncomputable def SourceRuns.paths : Set.range U.emission.emit ≃ Raw G input :=
  (Equiv.ofInjective U.tapes U.tapes_injective).trans (Equiv.subtypeEquivRight fun bs => by
    rw [U.accepts bs]
    simp only [and_true])

@[simp] theorem SourceRuns.paths_tapes (p : Set.range U.emission.emit) : (U.paths p).val = U.tapes p := rfl

/-- Assemble the relocation contract using only the source classification, its
execution facts, and counter readback of the selected mathematical occurrence. -/
noncomputable def SourceRuns.execution (inc : X → Fin (labelCount G) → ℕ)
    (read : ∀ x a, (visited x (Auxiliary.counterBase G+a.val)).val = inc x a) :
    Execution G input X inc S H := by
  have h (p : Set.range U.emission.emit) := U.effects p (reports (U.paths p)) (rawRun (U.paths p))
  exact ⟨U.encoding, U.emission, U.paths, U.tag,
    fun p r hr => ((h p).2.2.2 r hr).1, fun p => (h p).1,
    fun p a => (congrArg Fin.val ((h p).2.1 a)).trans (read _ a),
    fun p => (h p).2.2.1, fun p r hr => ((h p).2.2.2 r hr).2⟩

end LiveProgram.PairStages.Group.CompressedPaths

namespace LiveProgram.LocalCount

open BurstRAM CutSchedule ChainAssignments ExponentTrace LiveHeader LiveHeaderProgram PairStages PairStages.Group

variable {G : Group} {S H : ℕ}

/-- The physical inputs at one nominated first-half group. -/
structure CompressedInput (W : Conditions G S H) (P : PairStageConditions G S H)
    (adv : Bits (profile G).advice) (fit : 1+labelCount G*expWidth G ≤ (profile G).delta) where
  /-- Assignment of all physical cuts for the chain containing the selected first-half pair
  group. -/
  cuts : AllCuts (profile G).h (profile G).delta
  /-- Zero-based index of the nominated pair group within the first half of the physical chain. -/
  i : Fin (2^(profile G).h)
  selected : physicalTag cuts (halves (profile G).h (.inl i)) = some .pair
  padding : ∀ side, Fields.ValidPadding (profile G) cuts (halves (profile G).h (.inl i)) .pair side
  /-- Prepared header-stage execution for this first-half group on its actual cuts and advice,
  furnishing the memory from which nominations are read. -/
  trace : Prepared W adv cuts (halves (profile G).h (.inl i)) .pair
  out : Output (profile G) (Header.base G.g) G.g.d W.word adv cuts (halves (profile G).h (.inl i)) .pair (memory trace)
  /-- Production-count nomination selected for this pair by the physical nomination stage. -/
  μ : Nominations.Nom G
  /-- Initialization and sparse-copy runs for the selected nomination, preparing the auxiliary
  pair memory with the header from the actual exterior cuts. -/
  branch : Auxiliary.PreparedBranch G (memory trace) i (PairedChain.headers adv (exteriorOf fit (fst cuts)) i)
    (Nominations.indexed G (Auxiliary.nominationFits G i (P.room i) P.width.le P.nominations) (memory trace) trace.tag) μ

variable {W : Conditions G S H} {P : PairStageConditions G S H} {adv : Bits (profile G).advice}
    {fit : 1+labelCount G*expWidth G ≤ (profile G).delta} (I : CompressedInput W P adv fit)

/-- Recover the primed exterior cut strings from the outgoing exterior fields of the first-half
physical cuts, starting with the width-zero initial cut. -/
abbrev CompressedInput.exterior := exteriorOf fit (fst I.cuts)
/-- Certify the nomination stage's address, word-width and clock requirements for the selected
group using the pair-stage conditions at its index. -/
abbrev CompressedInput.nominationFits := Auxiliary.nominationFits G I.i (P.room I.i) P.width.le P.nominations

include I in
theorem CompressedInput.shadowFit : Auxiliary.shadowBase G < 2^G.w := by
  have room := P.room I.i
  have positive : 0 < LiveAuxiliaryHeaders.span (Auxiliary.pairLengths G I.i) (Auxiliary.histLength G) := by
    simp [LiveAuxiliaryHeaders.span,PrimedInputRAM.Header.count]
  omega

variable {h Δ a t Z : ℕ} {Nom : Type}
    {Path : Exterior h Δ → Fin (2^h) → Nom → Type} [∀ ξ i μ, Fintype (Path ξ i μ)]
    (W : Conditions G S H) (P : PairStageConditions G S H)
    (order : Nominations.Nom G ≃ Nom) (hh : h = (profile G).h) (hd : Δ = (profile G).delta)
    (ha : a = (profile G).advice) (ht : t = labelCount G) (hz : Z = expWidth G)
    (advice : Bits a) (cut : 1+t*Z ≤ Δ) (inc : ∀ ξ i μ, Path ξ i μ → Fin t → ℕ)

theorem physicalFit (hd : Δ = (profile G).delta) (ht : t = labelCount G) (hz : Z = expWidth G)
    (cut : 1+t*Z ≤ Δ) : 1+labelCount G*expWidth G ≤ (profile G).delta := by
  simpa only [ht, hz, hd] using cut

/-- Transport a physical exterior cut assignment to the model using the equalities of chain
heights and cut widths. -/
abbrev modelExterior (hh : h = (profile G).h) (hd : Δ = (profile G).delta)
    (ξ : Exterior (profile G).h (profile G).delta) : Exterior h Δ :=
  cast (congrArg₂ Exterior hh hd).symm ξ

/-- Transport all model dimensions simultaneously, preserving the native index,
input memory and selected physical nomination. -/
theorem compressedObligation_of_inputExecution
    (native : ∀ I : CompressedInput W P (cast (congrArg Bits ha) advice) (physicalFit hd ht hz cut),
      let ξ := modelExterior hh hd I.exterior
      let i := I.i.cast (congrArg (2^·) hh).symm
      Nonempty (CompressedPaths.Execution G (I.branch.copy.memory ()) (Path ξ i (order I.μ))
        (fun q j => inc ξ i (order I.μ) q (j.cast ht.symm)) S H)) :
    compressedObligation W P order hh hd ha ht hz advice cut inc := by
  subst h; subst Δ; subst a; subst t; subst Z
  apply compressedCalls_of_execution W P order advice cut inc
  intro cuts i j mode pad tr out ξ F N μ B
  exact native ⟨cuts,i,mode,pad,tr,out,μ,B⟩

end LiveProgram.LocalCount

namespace FixedProgramDiagonal.Program

open BurstRAM Compression CursorNetwork LiveProgram PairStages PairStages.Group LocalCount
open ExponentTrace CutSchedule ChainAssignments LabelEvaluator PairSimulation

universe v
variable {D : FixedProgramDiagonal.Program} {n C : ℕ}
    {ht : 21 ≤ 2^(D.geometry n).w} {hf : 44 ≤ n^10000}
    {K : Type v} [Field K] {S : BlockSchedule K} {B : S.Templates} {hn : 2 ≤ n} {p : Nat.Primes}
    {M : Model p (B.compressorDegree n) (B.compressorEquations hn C)}
    (data : D.ScalarData B hn M)
    (processorFit : ProcessorInput.Fits D.literal n (D.geometry n).d (D.geometry n).H (D.geometry n).w)
    {u : PairExponents B.growthConstant} (V : D.VirtualPairs B u hn C)

variable (W : Conditions (D.executionGroup n ht hf) (2^(D.geometry n).d) (D.geometry n).H)
    (P : PairStageConditions (D.executionGroup n ht hf) (2^(D.geometry n).d) (D.geometry n).H)
    (hC : D.constants.circuitExponent = C) (hg : D.constants.motifLabels = Fintype.card B.Entry)
    (cut : 1+B.denseCount n C * D.counterWidth n ≤ n^D.constants.deltaPower)

private theorem width_eq : D.counterWidth n = expWidth (D.executionGroup n ht hf) := by
  unfold expWidth executionGroup Constants.Z Constants.height
  rw [eval_mul,PublicExpr.eval_natPow]
  rfl

/-- One checked physical branch for the fixed program's model. -/
abbrev VirtualPairs.PhysicalInput := CompressedInput W P
  (cast (congrArg Bits (adviceSizes (D := D) (n := n) (ht := ht) (hf := hf))) data.advice)
  (physicalFit deltas (physicalPairLabelCount hC hg).symm width_eq cut)

variable (I : VirtualPairs.PhysicalInput data W P hC hg cut)

/-- Express the selected physical first-half index in the fixed model's index type using the
equality of chain heights. -/
noncomputable abbrev VirtualPairs.modelIndex := I.i.cast (congrArg (2^·) (heights (D := D) (n := n) (ht := ht) (hf := hf))).symm

/-- First-half exterior cut data of the selected physical input, transported to the fixed
program's model dimensions. -/
noncomputable abbrev VirtualPairs.exterior := modelExterior heights deltas I.exterior

private theorem headers_cast {h Δ a h' Δ' a' : ℕ} (hh : h=h') (hd : Δ=Δ') (ha : a=a')
    (advice : Bits a) (ξ : Exterior h' Δ') (i : Fin (2^h'))
    (lengths : PairedChain.lengths h' Δ' a' i = PairedChain.lengths h Δ a (i.cast (congrArg (2^·) hh).symm)) :
    (lengths.symm ▸ PairedChain.headers advice (cast (congrArg₂ Exterior hh hd).symm ξ)
      (i.cast (congrArg (2^·) hh).symm)) = PairedChain.headers (cast (congrArg Bits ha) advice) ξ i := by
  subst h'; subst Δ'; subst a'
  rfl

/-- The compressed call reads the canonical virtual pair's own reset memory at
each address in this actual physical input's shadow. -/
theorem VirtualPairs.input_shadow (a : ℕ) :
    I.branch.copy.memory () ((Auxiliary.shadow (D.executionGroup n ht hf)).val+a) =
      (V.data data.advice (VirtualPairs.exterior data W P hC hg cut I)
        (VirtualPairs.modelIndex data W P hC hg cut I) (physicalNomination hC I.μ)).initial a := by
  let i := VirtualPairs.modelIndex data W P hC hg cut I
  let ξ := VirtualPairs.exterior data W P hC hg cut I
  have h := V.shadow_initial (ht := ht) (hf := hf) hC data.advice ξ i I.μ
    (m := memory I.trace)
    (N := Nominations.indexed (D.executionGroup n ht hf) I.nominationFits (memory I.trace) I.trace.tag)
  have eq := headers_cast heights deltas adviceSizes data.advice I.exterior I.i (physicalPairLengths i)
  let hdr : PrimedInputRAM.Header (D.pairLengths i) → Bool := PairedChain.headers data.advice ξ i
  change ((physicalPairLengths (ht := ht) (hf := hf) i).symm ▸ hdr) =
    PairedChain.headers (cast (congrArg Bits adviceSizes) data.advice) I.exterior I.i at eq
  rw [eq] at h
  exact h I.branch a

/-- Native schedule facts on this particular canonical monomial witness.
The expected motif flushes start with the actual memory of the copy stage. -/
noncomputable abbrev VirtualPairs.nativeRuns :=
  let ξ := VirtualPairs.exterior data W P hC hg cut I
  let i := VirtualPairs.modelIndex data W P hC hg cut I
  let μ := physicalNomination hC I.μ
  let X := (V.pairData data processorFit).Path ξ i μ
  CompressedPaths.SourceRuns (D.executionGroup n ht hf) (I.branch.copy.memory ()) X (fun q =>
    Counters.visit (Auxiliary.counterBase (D.executionGroup n ht hf)) (Auxiliary.histLength (D.executionGroup n ht hf))
      (fun (v : B.Entry → ℕ) k => v (physicalMotifOrder hg k)) (V.histograms data processorFit ξ i μ q)
      (I.branch.copy.memory ())) (2^(D.geometry n).d) (D.geometry n).H

set_option maxHeartbeats 1200000 in
/-- Actual source tapes, their costs and their histogram writes give the canonical
occurrences and increments expected by the compressed stage's linker. -/
noncomputable def VirtualPairs.nativeExecution (U : V.nativeRuns data processorFit W P hC hg cut I) :
    let ξ := VirtualPairs.exterior data W P hC hg cut I
    let i := VirtualPairs.modelIndex data W P hC hg cut I
    let μ := physicalNomination hC I.μ
    CompressedPaths.Execution (D.executionGroup n ht hf) (I.branch.copy.memory ()) ((V.pairData data processorFit).Path ξ i μ)
      (fun q j => increments data processorFit V ξ i μ q (j.cast (physicalPairLabelCount hC hg)))
      (2^(D.geometry n).d) (D.geometry n).H :=
  U.execution _ (fun q j => V.counterVisits_readback data processorFit (VirtualPairs.exterior data W P hC hg cut I)
    (VirtualPairs.modelIndex data W P hC hg cut I) hC hg I.μ I.out
    I.nominationFits I.trace.tag I.branch I.shadowFit q (j.cast (physicalPairLabelCount hC hg)))

/-- Source executions at all valid prepared groups supply the complete first-half
compressed-call obligation, with the model's exact occurrence type and field exponents. -/
theorem VirtualPairs.compressedCalls_of_nativeRuns
    (native : ∀ I : VirtualPairs.PhysicalInput data W P hC hg cut,
      Nonempty (V.nativeRuns data processorFit W P hC hg cut I)) :
    V.compressedCalls data processorFit W P hC hg cut := by
  classical
  apply compressedObligation_of_inputExecution
  intro I
  exact ⟨V.nativeExecution data processorFit W P hC hg cut I (native I).some⟩

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
