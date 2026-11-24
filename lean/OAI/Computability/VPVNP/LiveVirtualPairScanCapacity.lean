import OAI.Computability.VPVNP.LiveVirtualPairCanonicalScan

/-! # The normalized payload scan fits before choosing the model and branch -/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM Compression CursorNetwork CursorBounds LiveProgram LabelEvaluator Filter
open PairSimulation.LocalHistory
open private scanInput from OAI.Computability.VPVNP.PairSimulationScanTrace

universe v
variable {K : Type v} [Field K] {S : BlockSchedule K} (D : FixedProgramDiagonal.Program)
    (B : S.Templates) (u : PairExponents B.growthConstant)

/-- Every final width lies below one physical word address space. The
threshold precedes all finite-model labels and all descriptor choices. -/
theorem eventually_scanWidth (C : ℕ) (hb : max S.laneBits 5 ≤ D.addressFactor) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn C) [NeZero (virtualBits D.addressFactor n)]
      (p : Nat.Primes) (M : Model p (B.compressorDegree n) (B.compressorEquations hn C)),
      ∀ z : (V.selection (M := M)).Choices,
        ((V.selection (M := M)).finalState z).totalWidth < 2^wordBits D.addressFactor n := by
  filter_upwards [eventually_pairBranchBounds.{v,0} B u D.addressFactor hb,
    eventually_numeric B u D.addressFactor 1 hb (by decide)] with n all num hn V inst p M z
  let r := addressBits D.addressFactor n
  let R := processorCount D.addressFactor n
  have term := all.2.2 (laneLabels _ _ V.lanes) V.dimension le_rfl M.algebra (B.compressorValues hn M)
    (B.compressorValues_solution hn M)
  have hbucket : virtualBucket n = 2^roundedUp 1 4 n := by
    simp only [virtualBucket,roundedUp_eq,Nat.cast_one,Nat.cast_ofNat]
  unfold pairInput at term
  rw [hbucket] at term
  have tw : (((V.selection (M := M)).finalState z).totalWidth : ℝ) ≤ (R : ℝ)*(n : ℝ)^(1-u.θ/2 : ℝ) :=
    (term z).2.1
  have lepow : (n : ℝ)^(1-u.θ/2 : ℝ) ≤ n := by
    have base : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1≤n by omega)
    have theta : 0 < (u.θ : ℝ) := by exact_mod_cast u.theta_pos
    simpa using Real.rpow_le_rpow_of_exponent_le base (show (1-u.θ/2 : ℝ) ≤ 1 by linarith)
  have width : ((V.selection (M := M)).finalState z).totalWidth ≤ R*n := by
    exact_mod_cast tw.trans (mul_le_mul_of_nonneg_left lepow (Nat.cast_nonneg R))
  have nr : n ≤ R := by have := num.2.2.1; dsimp only [R]; omega
  have exponent : r+r < wordBits D.addressFactor n := by
    change r+r < (r+10)^4
    have h := Nat.pow_le_pow_right (Nat.succ_pos (r+9)) (by decide : 2≤4)
    nlinarith only [h]
  exact width.trans_lt ((Nat.mul_le_mul_left R nr).trans_lt (by
    change 2^r*2^r < 2^wordBits D.addressFactor n
    rw [← pow_add]
    exact Nat.pow_lt_pow_right (by decide) exponent))

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
