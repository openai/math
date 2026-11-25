import OAI.Computability.BorderVNP.DiagonalCubeDeclarationRoom
import OAI.Computability.BorderVNP.PackedTerminalShape

/-! # Scaled operands of the selected cube's native memory allocation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter TeamScales Crossing PackedHistoryCircuit.Normalized _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical

universe u
variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {e : PaidIdentity F D m}
    {S : SiteSchedule e} {extra E dlog Q A B j : ℕ}

/-- The rounded alphabet, exterior volume and block count used by the native
header installation have positive size. Its million-scaled team budget fits
the actual arithmetic word. -/
theorem JointSchedule.eventually_cube_primitives {K : Type*} [Field K] (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{u} s (E+1) dlog Q A B j) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      let R := b.physical.teamsPred n+1
      let ξ := (s.τ:ℝ)/5
      let symbols := Cube.alphabet s.α n
      let X := R*exterior ξ r n
      let blocks := blocksFor X (cube.h*cube.b) (symbols^(cube.pred+1))
      1 ≤ symbols ∧ symbols ≤ n ∧ R ≤ n ∧ 1 ≤ X ∧ X ≤ (r*n+1)^2 ∧
        0 < blocks ∧ 1000000 < 2^b.physical.word n ∧ 1000000*X < 2^b.physical.word n := by
  filter_upwards [b.eventually_lengths 0,b.eventually_word_capacity 1000000 2,eventually_ge_atTop 1]
    with n lengths room hn
  intro r R ξ symbols X blocks
  have one : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have τpos : 0 < (s.τ:ℝ) := by exact_mod_cast s.tau_pos
  have xpos : 0 < 1-ξ := by dsimp only [ξ]; linarith only [s.alpha_small,s.tau_small]
  have sy : 0 < symbols := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by positivity : 0 < (n:ℝ)) _)
  have sb : symbols ≤ n := Nat.ceil_le.mpr ((Real.rpow_le_rpow_of_exponent_le one
    (by linarith only [s.alpha_small] : 3*(s.α:ℝ) ≤ 1)).trans_eq (Real.rpow_one _))
  have teams : R ≤ n := by
    have bounded := lengths.teams.2.trans ((Real.rpow_le_rpow_of_exponent_le one
      (by linarith only [s.alpha_small] : 2*(s.α:ℝ) ≤ 1)).trans_eq (Real.rpow_one _))
    exact_mod_cast bounded
  have lane : TeamScales.width n (1-ξ) ≤ n := by
    have upper := Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le one
      (by dsimp only [ξ]; linarith only [τpos] : 1-ξ ≤ 1))
    simpa [TeamScales.width] using upper
  have lanePos : 1 ≤ TeamScales.width n (1-ξ) := Nat.le_floor (by simpa using Real.one_le_rpow one xpos.le)
  have hr := stretch_one b.ρ n
  have xp : 0 < X := Nat.mul_pos (Nat.succ_pos _) (Nat.mul_pos hr lanePos)
  have nn : n ≤ r*n+1 := (Nat.le_mul_of_pos_left n hr).trans (Nat.le_succ _)
  have size : X ≤ (r*n+1)^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul (teams.trans nn) ((Nat.mul_le_mul_left r lane).trans (Nat.le_succ _))
  have blockPos : 0 < blocks := Nat.ceil_pos.mpr (div_pos (by positivity)
    (Nat.cast_pos.mpr (Nat.mul_pos cube.block_pos (pow_pos (pow_pos sy _) _))))
  have million := (Nat.mul_le_mul_left 1000000 size).trans_lt room.2.2.1
  exact ⟨sy,sb,teams,xp,size,blockPos,(Nat.le_mul_of_pos_right _ xp).trans_lt million,million⟩

/-- The actual fixed cube allocates at least one endpoint bit in each packet
bank, including a packet whose selector or supply width is zero. -/
theorem FixedCube.packet_bank_pos {K : Type*} [Field K] (cube : FixedCube K) :
    0 < Cube.Tally.bankWidth cube.pred cube.b cube.h cube.copies cube.width := by
  have ends : 0 < Fintype.card (Cube.Ends cube.pred)*(cube.h*cube.b) :=
    Nat.mul_pos Fintype.card_pos cube.block_pos
  unfold Cube.Tally.bankWidth Cube.Tally.supplyBase
  omega

end Diagonal

end BorderVNP
end Computability
end OAI
