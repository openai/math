import OAI.Computability.VPVNP.LiveVirtualPairs
import OAI.Computability.VPVNP.LiveLocalGroupCount

/-!
# Assembling the certificate on the fixed live instruction table

The live dispatcher uses lengths computed by public arithmetic; the
diagonal theorem describes them by powers of n. The two continuation
contracts below transport the same physical cuts between these length
notations. The virtual coefficient counter and the evaluator consume
the advice field of a single scalar model. Their path counts then fill
the local certificate for the actual processor program.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram

open BurstRAM CutSchedule ChainAssignments ExponentTrace LiveEvaluatorEncoding
open PairStages LocalCount

variable {G : Group} {R H h Δ a t Z M : ℕ} (W : Conditions G R H)
variable (hh : h = (profile G).h) (hΔ : Δ = (profile G).delta) (ha : a = (profile G).advice)
variable (adv : Bits a) (fit : 1+t*Z ≤ Δ)

section Pair
variable {Nom : Type*} [Fintype Nom] {Path : Exterior h Δ → Fin (2^h) → Nom → Type*}
  [∀ ξ i μ, Fintype (Path ξ i μ)]

/-- The pair continuation on the mathematical lengths of the fixed program. -/
def pairObligation (inc : ∀ ξ i μ, Path ξ i μ → Fin t → ℕ) : Prop := by
  subst h
  subst Δ
  subst a
  exact PairContinuation W adv fit inc

end Pair

/-- The tail continuation on the same lengths, advice and initial states. -/
def tailObligation (layout : LiveEvaluatorTail.Layout G.evaluator.extra M G.w Δ)
    (init : (Fin t → ℕ) → Code G.evaluator.extra M) : Prop := by
  subst h
  subst Δ
  subst a
  exact TailContinuation W adv fit layout init

variable {Nom : Type*} [Fintype Nom] {Path : Exterior h Δ → Fin (2^h) → Nom → Type*}
  [∀ ξ i μ, Fintype (Path ξ i μ)] (inc : ∀ ξ i μ, Path ξ i μ → Fin t → ℕ)
  (layout : LiveEvaluatorTail.Layout G.evaluator.extra M G.w Δ) (init : (Fin t → ℕ) → Code G.evaluator.extra M)

theorem checked_group (he : (profile G).e = t*Z) (hc : (profile G).config = fieldWords M*G.w)
    (pair : pairObligation W hh hΔ ha adv fit inc) (tail : tailObligation W hΔ ha adv fit layout init)
    (cuts : AllCuts h Δ) (j : Fin (2^(h+1))) :
    Nat.card (ActualPaths (machine G.constants G.evaluator G.pair G.g G.lit).program G.clock 0
      (LiveHeader.physicalMemory (d := G.g.d) W.word adv cuts j) (withinCaps R H)) =
    specifiedGroupCount fit inc G.evaluator layout init cuts j := by
  subst h
  subst Δ
  subst a
  exact LocalCount.group W adv fit inc layout init he hc pair tail cuts j

end LiveProgram

namespace FixedProgramDiagonal.Program

open Compression CursorNetwork LabelEvaluator BurstRAM LiveProgram CutSchedule ExponentTrace LiveEvaluatorEncoding
open JointLabelSystem

/-- Classical decidable equality for productions used when assembling a fixed program's
certificate. -/
noncomputable local instance (n C : ℕ) : DecidableEq (Production n C) := Classical.decEq _

universe v
variable {K : Type v} [Field K] {S : BlockSchedule K} (D : FixedProgramDiagonal.Program)
    (B : S.Templates) {n C : ℕ} (hn : 2 ≤ n)

/-- Assemble the live stage group from the fixed evaluator, pair, geometry, literal prefix, and
the clock n^10000. -/
noncomputable def executionGroup (n : ℕ) (ht : 21 ≤ 2^(D.geometry n).w) (hf : 44 ≤ n^10000) : PairStages.Group :=
  ⟨D.constants,D.evaluator,D.pair,D.geometry n,CounterPublic.actualPrefix D.literal,n^10000,ht,hf⟩

/-- The physical metadata agrees with the certificate's six mathematical
field lengths, including the complete evaluator word image. -/
theorem profile_eq {ht hf} (hC : D.constants.circuitExponent = C)
    (hg : D.constants.motifLabels = Fintype.card B.Entry) :
    LocalCount.profile (D.executionGroup n ht hf) =
      ⟨D.chainHeight n,n^D.constants.deltaPower,n^D.constants.advicePower,
        B.denseCount n C * D.counterWidth n, fieldWords (n^D.constants.radiusPower) * (D.geometry n).w⟩ := by
  unfold LocalCount.profile Header.sizes executionGroup Constants.lengths Lengths.eval
  simp only [Constants.labels, eval_add, Constants.grammarLabels_eq, hg, hC,
    Constants.height, Constants.Z, Constants.configWords, Constants.radius, eval_mul,
    PublicExpr.eval_natPow, PublicExpr.eval, chainHeight, counterWidth, geometry]
  rfl

variable {D B hn} {p : Nat.Primes} {M : Model p (B.compressorDegree n) (B.compressorEquations hn C)}
    (data : D.ScalarData B hn M)
    (processorFit : ProcessorInput.Fits D.literal n (D.geometry n).d (D.geometry n).H (D.geometry n).w)
    {u : PairExponents B.growthConstant} (V : D.VirtualPairs B u hn C)

/-- The dense production exponents credited to a compressed path, computed from its motif
counts and the selected nomination. -/
noncomputable abbrev increments :=
  let paths := V.pairData data processorFit
  fun ξ i μ (q : paths.Path ξ i μ) => B.denseExponent (fun j => (μ j).val) (paths.ν ξ i μ q)

variable {ht : 21 ≤ 2^(D.geometry n).w} {hf : 44 ≤ n^10000}
variable (W : LocalCount.Conditions (D.executionGroup n ht hf) (2^(D.geometry n).d) ((D.geometry n).H))
variable (hC : D.constants.circuitExponent = C) (hg : D.constants.motifLabels = Fintype.card B.Entry)
variable (cutFit : 1+B.denseCount n C * D.counterWidth n ≤ n^D.constants.deltaPower)
variable (image : LiveEvaluatorTail.Layout D.evaluator.extra (n^D.constants.radiusPower) (D.geometry n).w
    (n^D.constants.deltaPower))

theorem heights : D.chainHeight n = (LocalCount.profile (D.executionGroup n ht hf)).h := by
  change n^D.constants.chainPower-1 = (D.constants.lengths.eval (D.geometry n)).h
  simp [Constants.lengths, Lengths.eval, Constants.height, PublicExpr.eval, geometry]

theorem deltas : n^D.constants.deltaPower = (LocalCount.profile (D.executionGroup n ht hf)).delta := by
  change _ = (D.constants.lengths.eval (D.geometry n)).delta
  simp [Constants.lengths, Lengths.eval, PublicExpr.eval, geometry]

theorem adviceSizes : n^D.constants.advicePower = (LocalCount.profile (D.executionGroup n ht hf)).advice := by
  change _ = (D.constants.lengths.eval (D.geometry n)).advice
  simp [Constants.lengths, Lengths.eval, PublicExpr.eval, geometry]

/-- Construct the actual single-length certificate. Its only stage premises
are the successful native pair and tail continuations on the selected
compressed occurrence type and the selected evaluator input. -/
noncomputable def assembleLocalCertificate (zero : D.initialLiteral = 0)
    (hcap : 2^(D.geometry n).d * (D.geometry n).H < 2^(D.geometry n).w)
    (hR : 4*n ≤ 2^(D.geometry n).d) (hZ : D.chainHeight n + 2*(D.geometry n).d ≤ D.counterWidth n)
    (pair : pairObligation W heights deltas adviceSizes data.advice cutFit (increments data processorFit V))
    (tail : tailObligation W deltas adviceSizes data.advice cutFit image data.init) :
    D.Certificate B hn M processorFit where
  hw := W.word
  hc := hcap
  hR := hR
  hZ := hZ
  advice := data.advice
  fit := cutFit
  layout := image
  Path := (V.pairData data processorFit).Path
  pathFintype := (V.pairData data processorFit).pathFintype
  ν := (V.pairData data processorFit).ν
  hν := (V.pairData data processorFit).bounded
  hpair := (V.pairData data processorFit).weight
  initial := D.initial n data.raw
  init := data.init
  hi := data.init_state
  histories := data.histories
  htail := data.value
  group cuts j := by
    have shape := profile_eq D B (ht := ht) (hf := hf) hC hg
    have he := congrArg LiveHeaderSchedule.Sizes.e shape
    have hc := congrArg LiveHeaderSchedule.Sizes.config shape
    have h := checked_group W heights deltas adviceSizes data.advice cutFit (increments data processorFit V)
      image data.init he hc pair tail cuts j
    have hzero : Fin.ofNat (2^(D.geometry n).w) D.initialLiteral = 0 := by
      rw [zero]
      apply Fin.ext
      simp
    rw [hzero]
    exact h

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
