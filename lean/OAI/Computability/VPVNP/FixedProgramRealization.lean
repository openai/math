import OAI.Computability.VPVNP.LiveCertificateAssembly
import OAI.Computability.VPVNP.FixedProgramReaderData
import OAI.Computability.VPVNP.FixedProgramParameters
import OAI.Computability.VPVNP.FixedProgramOperandFits

/-!
# Realization at all admissible exceptional lengths

Once a literal program and its powers have been chosen, take a common
length threshold for its operand loader, its auxiliary coefficient counters,
and its two native continuations. A prime and a model may now be given at
that length. Use the canonical presentation computed by the reader to fill
the scalar certificate. The same advice, field values and virtual paths are
used on both halves of the chain.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM Compression LiveProgram CursorNetwork LabelEvaluator Filter
open RAMTape LiveProgram.LocalCount JointLabelSystem

attribute [local irreducible] Pieces.count rows LiveProgram.operand InputOperandMachine.geometryOnly
  PublicExpr.Fits OperandFits

set_option maxHeartbeats 400000
set_option exponentiation.threshold 10000

/-- Classical equality on the bounded production labels used to assemble the native
realization. -/
noncomputable local instance realizationProductionDecidable (n C : ℕ) : DecidableEq (Production n C) := Classical.decEq _

universe v
variable {K : Type v} [Field K] {S : BlockSchedule K} (D : FixedProgramDiagonal.Program)
    (B : S.Templates) (u : PairExponents B.growthConstant)

theorem tagsFit (n : ℕ) : 21 ≤ 2^(D.geometry n).w := by
  have w : 5 ≤ (D.geometry n).w := by
    change 5 ≤ (CursorBounds.addressBits D.addressFactor n+10)^4
    exact (by decide : 5 ≤ 10^4).trans (Nat.pow_le_pow_left (Nat.le_add_left ..) _)
  exact (by decide : 21 ≤ 2^5).trans (Nat.pow_le_pow_right (by decide) w)

theorem dispatchClock {n : ℕ} (hn : 2 ≤ n) : 44 ≤ n^10000 :=
  (by decide : 44 ≤ 2^6).trans ((Nat.pow_le_pow_left hn 6).trans
    (Nat.pow_le_pow_right (by omega : 0 < n) (by decide : 6 ≤ 10000)))

/-- Native statements only on prepared groups at this one length. All
objects come from the public virtual layout and the same scalar data. -/
def NativeContinuations (C n : ℕ) : Prop :=
  ∀ (hn : 2 ≤ n) (p : Nat.Primes) (M : Model p (B.compressorDegree n) (B.compressorEquations hn C))
    (data : D.ScalarData B hn M)
    (fit : ProcessorInput.Fits D.literal n (D.geometry n).d (D.geometry n).H (D.geometry n).w)
    (V : D.VirtualPairs B u hn C)
    (W : Conditions (D.executionGroup n (D.tagsFit n) (dispatchClock hn)) (2^(D.geometry n).d) (D.geometry n).H)
    (cut : 1+B.denseCount n C*D.counterWidth n ≤ n^D.constants.deltaPower)
    (image : LiveEvaluatorTail.Layout D.evaluator.extra (n^D.constants.radiusPower)
      (D.geometry n).w (n^D.constants.deltaPower)),
    pairObligation W heights deltas adviceSizes data.advice cut (increments data fit V) ∧
      tailObligation W deltas adviceSizes data.advice cut image data.init

/-- The readers and native continuations of a single fixed program supply
the local certificates uniformly in length, prime and input model. -/
theorem realizes_of_continuations (q C ports : ℕ) (env : ℕ → ℕ)
    (hC : D.constants.circuitExponent = C) (hg : D.constants.motifLabels = Fintype.card B.Entry)
    (zero : D.initialLiteral = 0) (hnumerator : D.numerator = (liveRatio u).num)
    (hdenominator : D.denominator = (liveRatio u).den)
    (hb : max S.laneBits 5 ≤ D.addressFactor)
    (hB : max (max (D.constants.chainPower+1) (D.constants.chainPower+D.constants.deltaPower))
      (max D.constants.advicePower (grammarCapacityPower C)) + 2 ≤ D.addressFactor)
    (selected : ∀ᶠ n : ℕ in atTop, Numerics B D C env ports n ∧
      ∀ (hn : 2 ≤ n) (p : Nat.Primes), (q ≠ 0 → p.val=q) →
      (q=0 → p.val ≤ 2^B.compressorPrimeBits C n) →
      ∀ M : Model p (B.compressorDegree n) (B.compressorEquations hn C),
        Nonempty (D.ScalarData B hn (canonicalModel B hn M)))
    (native : ∀ᶠ n : ℕ in atTop, D.NativeContinuations B u C n) : D.Realizes B q C := by
  unfold Realizes
  filter_upwards [D.eventually_operandFits B u hnumerator hdenominator,
    D.eventually_virtualPairs B u C hnumerator hdenominator hb hB,selected,native] with n ops virtual selection routes
  obtain ⟨sizes,scalar⟩ := selection
  refine ⟨ops,?_⟩
  intro hn p positive zeroChar M₀ fit
  obtain ⟨M⟩ := M₀
  obtain ⟨data⟩ := scalar hn p positive zeroChar M
  obtain ⟨V⟩ := virtual hn
  let G := D.executionGroup n (D.tagsFit n) (dispatchClock hn)
  have W := sizes.group G rfl rfl rfl le_rfl
  obtain ⟨pair,tail⟩ := routes hn p (canonicalModel B hn M) data fit V W sizes.counters sizes.layout
  exact ⟨canonicalModel B hn M,⟨assembleLocalCertificate data fit V W hC hg sizes.counters sizes.layout
    zero sizes.hc sizes.hR sizes.hZ pair tail⟩⟩

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
