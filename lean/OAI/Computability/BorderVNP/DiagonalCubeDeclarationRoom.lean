import OAI.Computability.BorderVNP.DiagonalJointPacketOccurrences
import OAI.Computability.BorderVNP.RoutingISACubeArenaGeometryRate

/-! # Capacity of the cube declaration on the calibrated physical layout -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

/-- The public declaration bound, including its reserved singleton slots, is
at most a fixed multiple of the actual padded volume. -/
theorem declarationCap_le_padded (n d blocks b h s : ℕ) (pos : 0 < h*b) :
    declarationCap n d blocks b h s ≤ (h*s+1)*padded n d blocks (h*b) := by
  have room := RoutingISA.CubeArena.declarationCap_le n d blocks b h s
  have unweighted : blocks*(d^(n+1))^2 ≤ padded n d blocks (h*b) :=
    Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ pos)
  calc
    _ ≤ _ := room
    _ ≤ padded n d blocks (h*b)*(h*s) + (d^(n+1))^2*(blocks*(h*b)) :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ unweighted) _
    _ = _ := by unfold padded; ring

end Cube.Physical

namespace Diagonal

open Filter TeamScales Crossing PackedHistoryCircuit.Normalized _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical

universe u

variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {e : PaidIdentity F D m}
    {S : SiteSchedule e} {extra E d Q A B j : ℕ}

/-- The uniform block rounding used by the physical packet embedding gives
a polynomial bound on all padded slots and room for every declaration code,
including the exclusive endpoint used by the native word decoder. -/
theorem JointSchedule.eventually_declaration_room {K : Type*} [Field K] (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{u} s (E+1) d Q A B j) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      let R := b.physical.teamsPred n+1
      let ξ := (s.τ:ℝ)/5
      let symbols := Cube.alphabet s.α n
      ∀ W : ℝ, W ≤ (R*exterior ξ r n : ℕ) →
        let blocks := blocksFor W (cube.h*cube.b) (symbols^(cube.pred+1))
        padded cube.pred symbols blocks (cube.h*cube.b) ≤ 5*(r*n+1)^2 ∧
          declarationCap cube.pred symbols blocks cube.b cube.h cube.width+1 < 2^b.physical.word n := by
  let C := (cube.h*cube.width+1)*5
  filter_upwards [b.eventually_placement cube 0,b.eventually_lengths 0,b.eventually_word_capacity (C+1) 2,
    eventually_ge_atTop 1] with n placement lengths words hn
  intro r R ξ symbols W budget blocks
  let Z := symbols^(cube.pred+1)
  let X := exterior ξ r n*R
  have room := placement.2.2.2.1
  change blocksFor (X:ℝ) (cube.h*cube.b) Z * (cube.h*cube.b) * Z^2 ≤ 5*X at room
  have mono : blocks ≤ blocksFor (X:ℝ) (cube.h*cube.b) Z := by
    apply blocksFor_mono
    simpa only [X,Nat.mul_comm R] using budget
  have pad : padded cube.pred symbols blocks (cube.h*cube.b) ≤ 5*X :=
    (Nat.mul_le_mul_right (Z^2) (Nat.mul_le_mul_right (cube.h*cube.b) mono)).trans room
  have one : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have teams : R ≤ n := by
    have upper := lengths.teams.2.trans (Real.rpow_le_rpow_of_exponent_le one
      (by linarith only [s.alpha_small] : 2*(s.α:ℝ) ≤ 1))
    rw [Real.rpow_one] at upper
    exact_mod_cast upper
  have τpos : 0 < (s.τ:ℝ) := by exact_mod_cast s.tau_pos
  have lane : TeamScales.width n (1-ξ) ≤ n := by
    have exp : 1-ξ ≤ 1 := by dsimp only [ξ]; linarith only [τpos]
    have upper := Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le one exp)
    simpa [TeamScales.width] using upper
  have nn : n ≤ r*n+1 := (Nat.le_mul_of_pos_left n (stretch_one b.ρ n)).trans (Nat.le_succ _)
  have total : X ≤ (r*n+1)^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul ((Nat.mul_le_mul_left r lane).trans (Nat.le_succ _)) (teams.trans nn)
  have bits := pad.trans (Nat.mul_le_mul_left 5 total)
  have cap := (declarationCap_le_padded cube.pred symbols blocks cube.b cube.h cube.width cube.block_pos).trans
    (Nat.mul_le_mul_left _ bits)
  have cap' : declarationCap cube.pred symbols blocks cube.b cube.h cube.width ≤ C*(r*n+1)^2 := by
    simpa only [C,Nat.mul_assoc] using cap
  have positive : 1 ≤ (r*n+1)^2 := Nat.pow_pos (Nat.succ_pos _)
  refine ⟨bits,lt_of_le_of_lt ?_ words.2.2.1⟩
  simpa only [Nat.add_mul,Nat.one_mul] using Nat.add_le_add cap' positive

end Diagonal

end BorderVNP
end Computability
end OAI
