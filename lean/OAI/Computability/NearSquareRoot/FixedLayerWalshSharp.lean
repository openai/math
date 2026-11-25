import OAI.Computability.NearSquareRoot.FixedLayerWalshProfile
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetInput
import OAI.Computability.NearSquareRoot.PhysicalWalshRouterClock

/-! # Packed recursive traces at the Walsh row's sparse clock -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace FixedLayer

open IntegerMultiplication Code FixedPoint DigitPacking Filter
open PhysicalWalsh PhysicalWalsh.GatherProgram PhysicalWalshNode KernelPass
  KernelPass.ComputableSyntax PhysicalWalshCompile.Dispatch EffectiveBoundedTask

/-- The measured packed piece and position router give a sharp release once
the operand's address width reaches the selected template's cutoff. -/
theorem WalshSharpRelease.of_packed {num den : ℕ} {r : Raw} (sel : Selected num den r)
    {router piece : Cmd} {ρ B c : ℝ} {Kpos K d : ℕ}
    (positive : 0 < ρ) (hB : 0 ≤ B) (hc : 0 ≤ c) (route : PositionRunsAt router ρ Kpos)
    (raw : let hw : 0 < (dimensions r).2 := (show 0 < 2 by decide).trans_le sel.wide
      Runs piece (fun v : PhysicalWalshNode.Admitted hw sel.plan =>
        pieceTimeBound ((dimensions r).1+1) sel.plan.calls ρ B RouterClock.logWidth
          (envelopeSetup K d (fun _ => 0)) v.val.shape)
        (fun v => pieceSpaceBound ((dimensions r).1+1) c (envelopeSetup K d (fun _ => 0)) v.val.shape)
        (rawInput hw sel.plan) (rawOutput hw sel.plan)) :
    ∃ cut, Nonempty (WalshSharpRelease sel router piece ρ cut) := by
  let H : ℝ := 96+3
  let Q : ℝ := K*((34*96:ℝ)^d+1)+0+1
  have width (k : ℕ) : (componentBits k:ℝ)+1 ≤ 96*((k:ℝ)+1) := by
    simp only [componentBits,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    linarith
  obtain ⟨cut,large⟩ := eventually_atTop.mp
    (addressBits_tendsto_atTop.eventually_ge_atTop (walshTemplateCut Kpos r))
  refine ⟨cut,⟨⟨B,c,H,Q,RouterClock.logWidth,envelopeSetup K d (fun _ => 0),max d 0,Kpos,
    positive,hB,hc,by norm_num [H],by dsimp [Q]; positivity,
    envelopeSetup_nonneg K d (fun _ => le_rfl),route,raw,large,?_,?_⟩⟩⟩
  · intro w _ k
    refine ⟨zero_le_one.trans (RouterClock.one_le_logWidth _),
      RouterClock.logWidth_linear_real (R:=96) (by norm_num) ?_⟩
    linarith [width k]
  · intro w _ k
    exact envelopeSetup_le_power (R:=96) (Q:=0) (by norm_num) le_rfl
      (by linarith [Nat.cast_nonneg (α:=ℝ) k]) (width k) (by simp)

/-- On a successful tuple the operand-linear arena and the row clock are
those certified by the sharp release in the total Walsh profile. -/
theorem walshProfile_rowClock {P : Type*} (arena clock : P → ℕ → ℕ) (cut : P → ℕ)
    {p : P} {ρ : ℝ} (hr : 0 ≤ ρ)
    (profile : ∀ w ≥ cut p, arena p w = w ∧ clock p w = max w (Pieces.sparseTime ρ (addressBits w))) :
    (∀ᶠ w in atTop, arena p w = w) ∧ RowClock ρ (clock p) :=
  SynchronizedPermutationBudget.profile_rowClock arena clock (fun _ w => Pieces.sparseTime ρ (addressBits w))
    cut hr (sparseTime_bound hr) profile

end FixedLayer

end

end NearSquareRoot
end Computability
end OAI
