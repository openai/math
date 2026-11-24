import OAI.Computability.VPVNP.LivePreparedPairCounters
import OAI.Computability.VPVNP.LiveVirtualPairReadback
import OAI.Computability.VPVNP.PairRAMCounterReadback

/-! # Reading the canonical compressed-pair increments in the live counter array

The grammar prefix in the actual post-copy memory already contains the nomination.
The final-site histogram visits add the compressor exponents to the zero motif suffix.
Both parts use the same dense order as the fixed program's exponent update.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM Compression CursorNetwork LiveProgram PairStages PairStages.Group
open ExponentTrace CutSchedule ChainAssignments LabelEvaluator JointLabelSystem PairSimulation

universe v
variable {D : FixedProgramDiagonal.Program} {n C : ℕ}
    {ht : 21 ≤ 2^(D.geometry n).w} {hf : 44 ≤ n^10000}
    {K : Type v} [Field K] {S : BlockSchedule K} {B : S.Templates}

theorem physicalGrammarCount (hC : D.constants.circuitExponent = C) :
    Auxiliary.histLength (D.executionGroup n ht hf) = FixedRows.productionCount n C := by
  change D.constants.grammarLabels.eval (D.geometry n) = _
  rw [D.constants.grammarLabels_eq, hC]
  rfl

/-- Numbering of the compressor labels in the suffix of the actual counter array. -/
noncomputable def physicalMotifOrder (hg : D.constants.motifLabels = Fintype.card B.Entry) :
    Fin D.constants.motifLabels ≃ B.Entry :=
  (finCongr hg).trans (Fintype.equivFin B.Entry).symm

theorem physicalDenseSize (hC : D.constants.circuitExponent = C) (hg : D.constants.motifLabels = Fintype.card B.Entry) :
    Auxiliary.histLength (D.executionGroup n ht hf) + D.constants.motifLabels = B.denseCount n C :=
  congrArg₂ Nat.add (physicalGrammarCount hC) hg

/-- The index transport from the exponent stage to the mathematical array keeps
the address ordinal of each counter. -/
theorem physicalPairLabelCount (hC : D.constants.circuitExponent = C) (hg : D.constants.motifLabels = Fintype.card B.Entry) :
    Group.labelCount (D.executionGroup n ht hf) = B.denseCount n C :=
  physicalDenseSize hC hg

theorem physicalPairCounterAddr (hs : Auxiliary.shadowBase (D.executionGroup n ht hf) < 2^(D.executionGroup n ht hf).w) (j : Fin (Group.labelCount (D.executionGroup n ht hf))) :
    (LiveExponent.counterAddr (D.executionGroup n ht hf).exponentPub j).val = Auxiliary.counterBase (D.executionGroup n ht hf) + j.val := by
  have base : ((D.executionGroup n ht hf).exponentPub 2).val = Auxiliary.counterBase (D.executionGroup n ht hf) := (Auxiliary.address_values (D.executionGroup n ht hf) hs).2.2.1
  have fit : ((D.executionGroup n ht hf).exponentPub 2).val + Group.labelCount (D.executionGroup n ht hf) ≤ 2^(D.executionGroup n ht hf).w := by
    rw [base]
    exact (Auxiliary.counter_end_le_shadow (D.executionGroup n ht hf)).trans hs.le
  exact (LiveExponent.counterAddr_val _ _ fit).trans (congrArg (· + j.val) base)

private theorem grammarEntry (hC : D.constants.circuitExponent = C) (μ : Nominations.Nom (D.executionGroup n ht hf))
    (j : Fin (FixedRows.productionCount n C)) :
    physicalNomination hC μ ((PrimedStackRAM.labelIndex n n _).symm j) =
      μ (j.cast (physicalGrammarCount (ht := ht) (hf := hf) hC).symm) := by
  subst C
  change μ ((Auxiliary.order (D.executionGroup n ht hf)) ((PrimedStackRAM.labelIndex n n _).symm j)) = _
  apply congrArg μ
  apply Fin.ext
  have h := congrArg (fun a : Fin (FixedRows.productionCount n D.constants.circuitExponent) => a.val)
    ((PrimedStackRAM.labelIndex n n (n^(D.constants.circuitExponent+5))).apply_symm_apply j)
  exact h

theorem physicalDenseExponent (hC : D.constants.circuitExponent = C) (hg : D.constants.motifLabels = Fintype.card B.Entry)
    (μ : Nominations.Nom (D.executionGroup n ht hf)) (ν : B.Entry → ℕ) (j : Fin (B.denseCount n C)) :
    Fin.addCases (fun i => (μ i).val) (fun i => ν (physicalMotifOrder hg i))
      (j.cast (physicalDenseSize (ht := ht) (hf := hf) hC hg).symm) =
      B.denseExponent (fun p => (physicalNomination hC μ p).val) ν j := by
  obtain ⟨(k | k), rfl⟩ := finSumFinEquiv.surjective j
  · let k' := k.cast (physicalGrammarCount (ht := ht) (hf := hf) hC).symm
    have index : (finSumFinEquiv (.inl k)).cast (physicalDenseSize (ht := ht) (hf := hf) hC hg).symm =
        k'.castAdd D.constants.motifLabels := Fin.ext rfl
    rw [index, Fin.addCases_left]
    simp only [BlockSchedule.Templates.denseExponent, Equiv.symm_apply_apply, Sum.elim_inl, Function.comp_apply]
    rw [grammarEntry]
  · let k' := k.cast hg.symm
    have index : (finSumFinEquiv (.inr k)).cast (physicalDenseSize (ht := ht) (hf := hf) hC hg).symm =
        k'.natAdd (Auxiliary.histLength (D.executionGroup n ht hf)) := by
      apply Fin.ext
      change FixedRows.productionCount n C + k.val = Auxiliary.histLength (D.executionGroup n ht hf) + k.val
      rw [physicalGrammarCount hC]
    rw [index, Fin.addCases_right]
    simp only [BlockSchedule.Templates.denseExponent, Equiv.symm_apply_apply, Sum.elim_inr, Function.comp_apply]
    rfl

private theorem stored_eq_of_readback {w b t : ℕ} (base : BurstRAM.Word w) (fit : base.val+t ≤ 2^w) (width : b ≤ w)
    (μ : Fin t → BurstRAM.Word b) (m : Memory w) (read : ∀ j : Fin t, (m (base.val+j.val)).val = (μ j).val) :
    LiveNominations.stored base fit μ m = m := by
  funext a
  by_cases h : base.val ≤ a ∧ a < base.val+t
  · let j : Fin t := ⟨a-base.val, by omega⟩
    have addr : a = base.val+j.val := by dsimp [j]; omega
    rw [addr]
    apply Fin.ext
    exact (LiveNominations.stored_at_val width base fit μ m j).trans (read j).symm
  · exact LiveNominations.stored_outside _ _ _ _ _ (by omega)

variable {hn : 2 ≤ n} {p : Nat.Primes}
    {M : Model p (B.compressorDegree n) (B.compressorEquations hn C)}
    (data : D.ScalarData B hn M)
    (processorFit : ProcessorInput.Fits D.literal n (D.geometry n).d (D.geometry n).H (D.geometry n).w)
    {u : PairExponents B.growthConstant} (V : D.VirtualPairs B u hn C)
    (ξ : Exterior (D.chainHeight n) (n^D.constants.deltaPower)) (i : D.groupIndices n)

/-- Final-site histograms of this precise virtual machine occurrence, using its private fuel. -/
noncomputable def VirtualPairs.histograms (μ : D.pairNom n C)
    (q : (V.pairData data processorFit).Path ξ i μ) : List (B.Entry → ℕ) :=
  let d := V.data data.advice ξ i μ
  pairRAMHistogramsWithFuel B u V.dimension V.cap (laneLabels _ _ V.lanes) le_rfl
    (B.compressorValues hn M) (B.compressorValues_solution hn M) d.machine d.fuel 0 d.initial q

variable (hC : D.constants.circuitExponent = C)
    (hg : D.constants.motifLabels = Fintype.card B.Entry) (μ : Nominations.Nom (D.executionGroup n ht hf))
    {m : Memory (D.executionGroup n ht hf).w} {hw : 4 ≤ (D.executionGroup n ht hf).w} {advice : Bits (Auxiliary.sizes (D.executionGroup n ht hf)).advice}
    {cuts : AllCuts (Auxiliary.sizes (D.executionGroup n ht hf)).h (Auxiliary.sizes (D.executionGroup n ht hf)).delta} {mode : LiveHeader.Mode.Tag}
    (out : LiveHeaderProgram.Output (Auxiliary.sizes (D.executionGroup n ht hf)) (Auxiliary.headerBase (D.executionGroup n ht hf)) (D.executionGroup n ht hf).g.d hw advice cuts
      (halves (Auxiliary.sizes (D.executionGroup n ht hf)).h (.inl (physicalPairIndex i))) mode m)
    (F : Nominations.Fits (D.executionGroup n ht hf)) (tag : (D.executionGroup n ht hf).tagged Stage.nominations m)
    {hdr : PrimedInputRAM.Header (Auxiliary.pairLengths (D.executionGroup n ht hf) (physicalPairIndex i)) → Bool}
    (P : Auxiliary.PreparedBranch (D.executionGroup n ht hf) m (physicalPairIndex i) hdr (Nominations.indexed (D.executionGroup n ht hf) F m tag) μ)
    (hs : Auxiliary.shadowBase (D.executionGroup n ht hf) < 2^(D.executionGroup n ht hf).w)
    (q : (V.pairData data processorFit).Path ξ i (physicalNomination hC μ))

include out hs

set_option maxHeartbeats 1200000 in
/-- The true post-copy memory followed by the canonical compressed-pair visits reads out
the fixed program's joint increments, at every dense counter address. -/
theorem VirtualPairs.counterVisits_readback (j : Fin (B.denseCount n C)) :
    let hist := V.histograms data processorFit ξ i (physicalNomination hC μ) q
    let final := Counters.visit (Auxiliary.counterBase (D.executionGroup n ht hf)) (Auxiliary.histLength (D.executionGroup n ht hf))
      (fun (v : B.Entry → ℕ) k => v (physicalMotifOrder hg k)) hist (P.copy.memory ())
    (final (Auxiliary.counterBase (D.executionGroup n ht hf)+j.val)).val = increments data processorFit V ξ i (physicalNomination hC μ) q j := by
  dsimp only
  let d := V.data data.advice ξ i (physicalNomination hC μ)
  let base := Auxiliary.counter (D.executionGroup n ht hf)
  have baseEq : base.val = Auxiliary.counterBase (D.executionGroup n ht hf) := (Auxiliary.address_values (D.executionGroup n ht hf) hs).2.2.1
  obtain ⟨prefixRead, suffixRead⟩ := P.initialCounters out F tag μ hs
  have pref (k : Fin (Auxiliary.histLength (D.executionGroup n ht hf))) : (P.copy.memory () (base.val+k.val)).val = (μ k).val := by
    rw [baseEq]; exact prefixRead k
  have suff (k : Fin D.constants.motifLabels) :
      P.copy.memory () (base.val+Auxiliary.histLength (D.executionGroup n ht hf)+k.val) = 0 := by
    rw [baseEq]; exact suffixRead k
  have stored := stored_eq_of_readback base F.address F.width_le μ (P.copy.memory ()) pref
  have degree := V.degree M.algebra (B.compressorValues hn M) (B.compressorValues_solution hn M)
    i (PairedChain.headers data.advice ξ i) (physicalNomination hC μ) q
  have read := pairRAMHistogramsWithFuel_readback B u V.dimension V.cap (laneLabels _ _ V.lanes) le_rfl
    (B.compressorValues hn M) (B.compressorValues_solution hn M) d.machine d.fuel 0 d.initial q degree
    (physicalMotifOrder hg) base F.address μ (P.copy.memory ()) suff
    (j.cast (physicalDenseSize (ht := ht) (hf := hf) hC hg).symm)
  dsimp only at read
  rw [← baseEq, ← stored]
  exact read.trans (physicalDenseExponent hC hg μ _ j)

/-- The native exponent stage sees the same increments at its actual word addresses. -/
theorem VirtualPairs.counterAddr_readback (a : Fin (Group.labelCount (D.executionGroup n ht hf))) :
    let hist := V.histograms data processorFit ξ i (physicalNomination hC μ) q
    let final := Counters.visit (Auxiliary.counterBase (D.executionGroup n ht hf)) (Auxiliary.histLength (D.executionGroup n ht hf))
      (fun (v : B.Entry → ℕ) k => v (physicalMotifOrder hg k)) hist (P.copy.memory ())
    (final (LiveExponent.counterAddr (D.executionGroup n ht hf).exponentPub a).val).val =
      increments data processorFit V ξ i (physicalNomination hC μ) q
        (a.cast (physicalPairLabelCount (ht := ht) (hf := hf) hC hg)) := by
  dsimp only
  rw [physicalPairCounterAddr hs a]
  exact V.counterVisits_readback data processorFit ξ i hC hg μ out F tag P hs q
    (a.cast (physicalPairLabelCount (ht := ht) (hf := hf) hC hg))

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
