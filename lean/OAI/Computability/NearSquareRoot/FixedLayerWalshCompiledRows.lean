import OAI.Computability.NearSquareRoot.FixedLayerWalshCompilerFor

/-! # The full effective Walsh row branch from physical routing instructions

The literal signed kernel selected by the enclosing scheduler also generates
the recursive piece code. Arbitrary guesses use its total physical
executions. A good guess has the sparse row clock and an eventual linear
arena for the same file.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

set_option maxHeartbeats 1800000
noncomputable section
namespace FixedLayer

open IntegerMultiplication Code Space FixedPoint FixedCandidate DigitPacking Filter
open KernelPass KernelPass.ComputableSyntax PhysicalWalsh PhysicalWalshNode
open PhysicalWalshCompile PhysicalWalshCompile.Dispatch PhysicalWalsh.GatherProgram
open CommonRegisters GeneratorSyntax EffectiveBoundedTask

/-- The only local program premises concern the actual, named physical bit
position router and flat controlled XOR opcodes. -/
theorem compiledWalshRowsFor {P : Type} [Primcodable P] {I : P → Type}
    (exponent : P → ℕ) (he : Computable exponent) (r : ℕ → Raw) (hs : Computable r)
    (valid : ∀ j,(interpreted (r j)).Good (j+3) (2*(j+2)))
    (flat : P × Raw → Op → Cmd) (ef : Effective ltr (Function.uncurry flat))
    (F : ℕ) (wf : ∀ y op,Within F (flat y op))
    (router : P → Cmd) (er : Effective ltr router) (R : ℕ) (wr : ∀ p,Within R (router p))
    (radius : P → ℕ) (rt : ∀ p,PositionTotalAt (router p) (radius p))
    (xt : ∀ p, TotalXorCosts (fun a => flat (p,a)) (r (exponent p)))
    (good : P → Prop)
    (rf : ∀ p,good p → ∃k, PositionRunsAt (router p) (Generator.midExponent (exponent p)) k)
    (xf : ∀ p,good p → SharpXorCosts (fun a => flat (p,a)) (r (exponent p))
      (Generator.midExponent (exponent p)) 0)
    (n : ∀ p,I p → ℕ) (hv : ∀ p i,Directory (n p i)) (dir : ∀ p,I p → Bool)
    (hd : ∀ p i,4 ≤ (box (n p i)).length) (hn : ∀ p i,2 ≤ n p i)
    (large : ∀ p i,walshTemplateCut (radius p) (r (exponent p)) ≤ addressBits (n p i)) :
    ∃ arena clock : P → ℕ → ℕ,
      EffectiveImplementsAt n hv dir hd arena clock .walsh ∧
      (∀ p w,w ≤ arena p w ∧ arena p w ≤ clock p w) ∧
      ∀ p,good p → (∀ᶠ w in atTop,arena p w = w) ∧ RowClock (Generator.midExponent (exponent p)) (clock p) := by
  obtain ⟨cmd,N,D,emit,_,_,reg,sel,run⟩ := compiledPieceProfilesFor r hs valid flat ef F wf
  let piece p := cmd (p,exponent p)
  have ep : Effective ltr piece := emit.comp (Computable.id.pair he)
  exact effectiveWalshPackedProfile (fun p => r (exponent p)) (hs.comp he) (fun p => sel (exponent p))
    router piece er ep (max R N) (fun p => RegisterSelect.within_mono (le_max_left ..) _ (wr p))
    (fun p => RegisterSelect.within_mono (le_max_right ..) _ (reg _)) n hv dir hd hn radius large rt
    (fun p => (run p (exponent p)).1 (xt p))
    good (fun p => Generator.midExponent (exponent p)) (fun p _ =>
      (show (0:ℝ)<1/2 by norm_num).trans (midpoint_bounds (exponent p)).1) rf
    (fun p ok => (run p (exponent p)).2 ((xf p ok).atDegree D))

end FixedLayer

end

end NearSquareRoot
end Computability
end OAI
