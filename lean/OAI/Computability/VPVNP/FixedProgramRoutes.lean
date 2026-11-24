import OAI.Computability.VPVNP.FixedProgramRealization
import OAI.Computability.VPVNP.LiveVirtualPairContinuation
import OAI.Computability.VPVNP.FixedProgramTailContinuation
import OAI.Computability.VPVNP.FixedProgramTailCaps

/-!
# The two native routes of the fixed program

The initialized tail, the remaining transitions and the non-evaluation
routes are determined by the program itself. The pair's compressed run is
entered only after the header, nomination and sparse-copy stages have
actually been executed. At every sufficiently large length their resource
bounds and the tail resource bounds hold for the same address multiplier.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM Compression LiveProgram CursorNetwork LabelEvaluator Filter
open LiveProgram.LocalCount LiveProgram.EvaluatorRoutes

universe v
variable {K : Type v} [Field K] {S : BlockSchedule K} (D : FixedProgramDiagonal.Program)
    (B : S.Templates) (u : PairExponents B.growthConstant) (C : ℕ)
    (hC : D.constants.circuitExponent = C) (hg : D.constants.motifLabels = Fintype.card B.Entry)

/-- The native compressed pair table produces the concrete finite path and
counter readback on each prepared input, within the actual live caps. -/
def PairRuns (n : ℕ) : Prop :=
  ∀ (hn : 2 ≤ n) (p : Nat.Primes) (M : Model p (B.compressorDegree n) (B.compressorEquations hn C))
    (data : D.ScalarData B hn M)
    (fit : ProcessorInput.Fits D.literal n (D.geometry n).d (D.geometry n).H (D.geometry n).w)
    (V : D.VirtualPairs B u hn C)
    (W : Conditions (D.executionGroup n (D.tagsFit n) (dispatchClock hn)) (2^(D.geometry n).d) (D.geometry n).H)
    (P : PairStageConditions (D.executionGroup n (D.tagsFit n) (dispatchClock hn)) (2^(D.geometry n).d) (D.geometry n).H)
    (cut : 1+B.denseCount n C*D.counterWidth n ≤ n^D.constants.deltaPower),
    V.compressedCalls data fit W P hC hg cut

/-- At any larger address multiplier, realizing the compressed table at
one length implies both complete native continuation counts at that length.
The threshold precedes the choice of the field model and its raw advice. -/
theorem eventually_native_of_pairRuns (c : Constants) (E : UniversalMachine.Program)
    (hc : c.circuitExponent = C) (hm : c.motifLabels = Fintype.card B.Entry) :
    ∃ b₀ : ℕ, ∀ b ≥ b₀, ∀ (hb : 1 ≤ b) (O : PairTable),
      let D := ofPaperConstants c E O b hb (liveRatio u)
      ∀ᶠ n : ℕ in atTop, D.PairRuns B u C hc hm n → D.NativeContinuations B u C n := by
  obtain ⟨b₁,h₁⟩ := eventually_pairStageConditions u c
  obtain ⟨b₂,h₂⟩ := eventually_tailFits u c E
  refine ⟨max b₁ b₂,?_⟩
  intro b hbig hb O D
  filter_upwards [h₁ b ((le_max_left ..).trans hbig),h₂ b ((le_max_right ..).trans hbig)] with n stages tails
  intro runs hn p M data fit V W cut image
  let G := D.executionGroup n (D.tagsFit n) (dispatchClock hn)
  have geom : G.g = paperGeometry b (liveCapacity u) n := rfl
  have P := stages G rfl geom le_rfl
  have room : data.raw.length ≤ G.constants.prefixCapacity.eval G.g := by
    rw [Constants.prefixCapacity,PublicExpr.eval_natPow]
    exact data.rawLength
  have F := tails G geom rfl rfl le_rfl data.raw.length room
  exact ⟨V.pairObligation data fit W P hc hm cut (runs hn p M data fit V W P cut),
    fixedTailObligation data W hc hm cut image F.fits F.geometry F.call F.ordinaryBudget F.initialBudget⟩

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
