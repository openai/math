import OAI.Computability.NearSquareRoot.PhysicalWalshEffectiveRoutesSelected
import OAI.Computability.NearSquareRoot.PhysicalWalshRectangleFamily
import OAI.Computability.NearSquareRoot.FixedLayerWalshCompiledRows

/-! # The actual selected Walsh row on every fixed arithmetic candidate

Both the global position permutation and the flat routing opcodes receive
the same binary rectangle source. On every reserve tuple the operand guard
admits the entire computed signed kernel. Sufficiently large low and high
reserves at a fixed midpoint exponent give an operand-linear arena.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

set_option maxHeartbeats 1800000
noncomputable section
namespace FixedCandidate.CandidateParameters

open IntegerMultiplication Code Space FixedPoint DigitPacking FixedLayer Filter
open KernelPass KernelPass.ComputableSyntax PhysicalWalsh PhysicalWalsh.GatherProgram
open CommonRegisters GeneratorSyntax

theorem selectedWalshRowProfile (F : InterchangeROMFamily.NativeFamily) (degree : ℕ) (dir : Bool) :
    ∃ arena clock : Guess → ℕ → ℕ,
      EffectiveImplementsAt (fun p (i : LargeInput (inputCut degree p)) => i.val.width)
        (fun _ i => (accepted_width i.property).1) (fun _ _ => dir)
        (fun _ i => (accepted_walsh i.property).1) arena clock .walsh ∧
      (∀ p w,w ≤ arena p w ∧ arena p w ≤ clock p w) ∧
      ∀ j, ∀ᶠ a in atTop, ∀ᶠ b in atTop, ∀ᶠ d in atTop,
        (∀ᶠ w in atTop,arena (j,a,b,d) w = w) ∧ RowClock (Generator.midExponent j) (clock (j,a,b,d)) := by
  obtain ⟨degreeRect,H,emit,er,run⟩ := InterchangeROMBinary.Selected.ofNative F
  let rect (j : ℕ) := emit (2*j+2)
  have rectEff : Effective ltr rect :=
    er.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp (.const 2) Primrec.id) (.const 2)).to_comp
  have rectBound j : Within H (rect j) := (run _).1
  have rectReady j : Controlled.Effective.rectContract (rect j) (Generator.midExponent j) := by
    refine ⟨degreeRect,?_⟩
    exact (native_exponent (j,0,0,0)) ▸ (run (2*j+2)).2
  obtain ⟨flat,M,ef,wf,xcost⟩ := PhysicalWalshEffectiveRoutes.profilesFromRectangle
    (fun p => rect (exponent p)) (rectEff.comp exponent_pr.to_comp) H
    (fun p => rectBound _) (fun p => rectReady _)
  let key (p : Guess) : RouteGuess := (exponent p,positionLow p,positionHigh p)
  have keyC : Computable key := exponent_pr.to_comp.pair (positionLow_pr.to_comp.pair positionHigh_pr.to_comp)
  let router p := guessedRouter rect (key p)
  have routeEff : Effective ltr router := (guessedRouter_effective rectEff).comp keyC
  obtain ⟨R,_,reg⟩ := guessedRouter_within H rectBound
  choose threshold route using guessedRouter_runs rectReady
  let good (p : Guess) := threshold (exponent p) ≤ positionLow p ∧ threshold (exponent p) ≤ positionHigh p
  have large (p : Guess) (i : LargeInput (inputCut degree p)) :
      walshTemplateCut 0 (signedTemplate p) ≤ addressBits i.val.width := by
    have h := (accepted_walsh i.property).2
    exact (max_le_max_right _ (Nat.zero_le (positionCutoff p))).trans h
  obtain ⟨arena,clock,task,bounds,fast⟩ := compiledWalshRowsFor exponent exponent_pr.to_comp
    computable_midpoint_templates.choose computable_midpoint_templates.choose_spec.1
    computable_midpoint_templates.choose_spec.2 flat ef M wf router routeEff R (fun p => reg (key p))
    (fun _ => 0) (fun p => guessedRouter_total rectReady (key p)) (fun p => (xcost p).1) good
    (fun p hp => ⟨0,route (exponent p) (positionLow p) (positionHigh p) hp.1 hp.2⟩)
    (fun p _ => (xcost p).2) (fun p (i : LargeInput (inputCut degree p)) => i.val.width)
    (fun _ i => (accepted_width i.property).1) (fun _ _ => dir) (fun _ i => (accepted_walsh i.property).1)
    (fun p i => (inputCut_ge_two degree p).trans i.property) large
  refine ⟨arena,clock,task,bounds,fun j => ?_⟩
  filter_upwards [eventually_ge_atTop (threshold j)] with a ha
  filter_upwards [eventually_ge_atTop (threshold j)] with b hb
  exact Filter.Eventually.of_forall (fun d => fast (j,a,b,d) ⟨ha,hb⟩)

end FixedCandidate.CandidateParameters

end

end NearSquareRoot
end Computability
end OAI
