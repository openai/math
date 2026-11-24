import OAI.Computability.VPVNP.LiveCertificateAssembly
import OAI.Computability.VPVNP.LiveNativePairContinuation

/-!
# First-half continuation for the fixed program's virtual pair witness

The production nominations use the physical parser order. The paths and
increments are exactly those of `VirtualPairs.pairData`, computed with the
auxiliary machine's own private fuel. This supplies the pair argument of
`assembleLocalCertificate` once its local compressed calls have been realized.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram

open BurstRAM CutSchedule ChainAssignments ExponentTrace PairStages LocalCount

variable {G : Group} {S H h Δ a t Z : ℕ} {Nom : Type*} [Fintype Nom]
    {Path : Exterior h Δ → Fin (2^h) → Nom → Type*} [∀ ξ i μ, Fintype (Path ξ i μ)]
    (W : Conditions G S H) (P : PairStageConditions G S H) (order : Group.Nominations.Nom G ≃ Nom)
    (hh : h = (profile G).h) (hΔ : Δ = (profile G).delta) (ha : a = (profile G).advice)
    (ht : t = Group.labelCount G) (hz : Z = Group.expWidth G)
    (adv : Bits a) (fit : 1+t*Z ≤ Δ) (inc : ∀ ξ i μ, Path ξ i μ → Fin t → ℕ)

/-- Compressed calls on the physical group, expressed with the fixed
program's mathematical dimensions and its exact path family. -/
def compressedObligation : Prop := by
  subst h; subst Δ; subst a; subst t; subst Z
  exact CompressedCalls W P order adv fit inc

theorem pairObligation_of_compressed
    (small : ∀ ξ i μ q v, inc ξ i μ q v < 2^(2*G.g.d))
    (native : compressedObligation W P order hh hΔ ha ht hz adv fit inc) :
    pairObligation W hh hΔ ha adv fit inc := by
  subst h; subst Δ; subst a; subst t; subst Z
  exact pairContinuation_of_compressed W P order adv fit inc small native

end LiveProgram

namespace FixedProgramDiagonal.Program

open Compression CursorNetwork LabelEvaluator BurstRAM LiveProgram CutSchedule ExponentTrace LiveProgram.LocalCount
open LiveProgram.PairStages.Group
open scoped Classical

/-- Classical decidable equality for the grammar productions at length n and circuit exponent
C, used locally to index production nominations. -/
noncomputable local instance (n C : ℕ) : DecidableEq (JointLabelSystem.Production n C) := Classical.decEq _

open private denseExponent_lt from OAI.Computability.VPVNP.FixedModelDiagonal

universe v
variable {K : Type v} [Field K] {S : BlockSchedule K} {D : FixedProgramDiagonal.Program}
    {B : S.Templates} {n C : ℕ} {hn : 2 ≤ n} {p : Nat.Primes}
    {M : Model p (B.compressorDegree n) (B.compressorEquations hn C)}
    (data : D.ScalarData B hn M)
    (processorFit : ProcessorInput.Fits D.literal n (D.geometry n).d (D.geometry n).H (D.geometry n).w)
    {u : PairExponents B.growthConstant} (V : D.VirtualPairs B u hn C)
    {ht : 21 ≤ 2^(D.geometry n).w} {hf : 44 ≤ n^10000}

/-- Reindex the dense nomination array by the production labels of the
very same virtual coefficient counter. -/
noncomputable def physicalNomination (hC : D.constants.circuitExponent = C) :
    Nominations.Nom (D.executionGroup n ht hf) ≃ D.pairNom n C :=
  (Auxiliary.nominationEquiv _).trans (Equiv.cast (congrArg (D.pairNom n) hC))

variable (W : Conditions (D.executionGroup n ht hf) (2^(D.geometry n).d) (D.geometry n).H)
    (P : PairStageConditions (D.executionGroup n ht hf) (2^(D.geometry n).d) (D.geometry n).H)
    (hC : D.constants.circuitExponent = C) (hg : D.constants.motifLabels = Fintype.card B.Entry)
    (cutFit : 1+B.denseCount n C * D.counterWidth n ≤ n^D.constants.deltaPower)

include hC hg in
private theorem labelDimension : B.denseCount n C = labelCount (D.executionGroup n ht hf) := by
  unfold labelCount executionGroup Constants.labels
  rw [eval_add,Constants.grammarLabels_eq]
  simp only [hg,hC,geometry,PublicExpr.eval]

private theorem exponentDimension : D.counterWidth n = expWidth (D.executionGroup n ht hf) := by
  unfold expWidth executionGroup Constants.Z Constants.height
  rw [eval_mul,PublicExpr.eval_natPow]
  rfl

/-- The native obligation for the physical inputs of `VirtualPairs.witness`.
That witness uses `d.machine d.fuel 0 d.initial` with `d := V.data ...`.
Its dense increments combine the nominated grammar counts with the
compression-label counts of that exact choice. -/
noncomputable abbrev VirtualPairs.compressedCalls :=
  compressedObligation W P (physicalNomination hC) heights deltas adviceSizes
    (labelDimension hC hg) exponentDimension data.advice cutFit (increments data processorFit V)

/-- The canonical first-half argument of `assembleLocalCertificate`.
The only remaining stage-specific premise is the native realization and
budget of the compressed subroutine. -/
theorem VirtualPairs.pairObligation (native : V.compressedCalls data processorFit W P hC hg cutFit) :
    LiveProgram.pairObligation W heights deltas adviceSizes data.advice cutFit (increments data processorFit V) := by
  apply pairObligation_of_compressed W P (physicalNomination hC) heights deltas adviceSizes
    (labelDimension hC hg) exponentDimension data.advice cutFit (increments data processorFit V) _ native
  intro ξ i μ q j
  exact denseExponent_lt B μ ((V.pairData data processorFit).ν ξ i μ q)
    ((V.pairData data processorFit).bounded ξ i μ q) j

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
