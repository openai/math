import OAI.Computability.BorderVNP.DiagonalJointPlacement
import OAI.Computability.BorderVNP.DiagonalJointWords

/-! # The global number of selected packet-vertex occurrences in the calibrated batch

Each vertex contributes at most one occurrence of a fixed gadget. The calibrated
physical packed-host volume bounds the number of vertices in all packets, including
packets belonging to other groups. This count fits the actual unsigned machine,
tally and private-multiplicity words simultaneously.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

/-- Each full packet has two vertices per unweighted padded incidence in its grouping
cut. Counting over all packets bounds the number of scalar occurrences globally. -/
theorem packet_vertex_card_le_padded (n d blocks width : ℕ) (hwidth : 0 < width) :
    Fintype.card (Packet n d blocks × Vertex (n+1)) ≤ 2*padded n d blocks width := by
  have count := packet_count n d blocks 1
  have weighted : padded n d blocks 1 ≤ padded n d blocks width := by
    unfold padded
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hwidth)
  rw [Fintype.card_prod,show Fintype.card (Vertex (n+1)) = 2^(n+1) by simp [Vertex,ZMod.card]]
  simpa only [Nat.mul_one,pow_succ,← Nat.mul_assoc,Nat.mul_comm 2] using
    Nat.mul_le_mul_right 2 (count.trans weighted)

/-- Rounding the true occupied volume to a uniform number of blocks is monotone
in the chosen total budget, including zero-sized allocations. -/
theorem blocksFor_mono {W X : ℝ} (le : W ≤ X) (width Z : ℕ) :
    blocksFor W width Z ≤ blocksFor X width Z :=
  Nat.ceil_mono (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left le (by norm_num)) (by positivity))

end Cube.Physical

namespace Diagonal

open Filter TeamScales Crossing PackedHistoryCircuit.Normalized _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical

universe u

variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {e : PaidIdentity F D m}
    {S : SiteSchedule e} {extra E d Q A B j : ℕ}

/-- At the actual §11.3 scales, the total number of possible packet-vertex
occurrences is at most `10*(r*n+1)^2`, and fits each of the three chosen words.
The native label budget is the product of the team count and the exterior volume. -/
theorem JointSchedule.eventually_packet_occurrences {K : Type*} [Field K] (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{u} s (E+1) d Q A B j) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      let R := b.physical.teamsPred n+1
      let ξ := (s.τ:ℝ)/5
      let symbols := Cube.alphabet s.α n
      ∀ W : ℝ, W ≤ (R*exterior ξ r n : ℕ) →
        let blocks := blocksFor W (cube.h*cube.b) (symbols^(cube.pred+1))
        let count := Fintype.card (Packet cube.pred symbols blocks × Vertex (cube.pred+1))
        count ≤ 10*(r*n+1)^2 ∧ count < 2^b.physical.word n ∧
          count < 2^b.physical.tally n ∧ count < 2^b.physical.multBits n := by
  filter_upwards [b.eventually_placement cube 0,b.eventually_lengths 0,b.eventually_word_capacity 10 2,
    eventually_ge_atTop 1] with n placement lengths words hn
  intro r R ξ symbols W budget blocks count
  let Z := symbols ^ (cube.pred+1)
  let X := exterior ξ r n * R
  have room := placement.2.2.2.1
  change blocksFor (X:ℝ) (cube.h*cube.b) Z * (cube.h*cube.b) * Z^2 ≤ 5*X at room
  have mono : blocks ≤ blocksFor (X:ℝ) (cube.h*cube.b) Z := by
    apply blocksFor_mono
    simpa only [X,Nat.mul_comm R] using budget
  have pad : padded cube.pred (Cube.alphabet s.α n) blocks (cube.h*cube.b) ≤ 5*X :=
    (Nat.mul_le_mul_right (Z^2) (Nat.mul_le_mul_right (cube.h*cube.b) mono)).trans room
  have one : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have teams : R ≤ n := by
    have bound := lengths.teams.2
    have exp : 2*(s.α:ℝ) ≤ 1 := by linarith only [s.alpha_small]
    have tight := bound.trans (Real.rpow_le_rpow_of_exponent_le one exp)
    rw [Real.rpow_one] at tight
    exact_mod_cast tight
  have tau : 0 < (s.τ:ℝ) := by exact_mod_cast s.tau_pos
  have xi : 0 ≤ ξ := div_nonneg tau.le (by norm_num)
  have lane : TeamScales.width n (1-ξ) ≤ n := by
    have exp : 1-ξ ≤ 1 := by linarith only [xi]
    have upper := Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le one exp)
    simpa [TeamScales.width] using upper
  have hr := stretch_one b.ρ n
  have nn : n ≤ r*n+1 := (Nat.le_mul_of_pos_left n hr).trans (Nat.le_succ _)
  have exteriorBound : exterior ξ r n ≤ r*n+1 := (Nat.mul_le_mul_left r lane).trans (Nat.le_succ _)
  have total : X ≤ (r*n+1)^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul exteriorBound (teams.trans nn)
  have bounded : count ≤ 10*(r*n+1)^2 := calc
    count ≤ 2*padded cube.pred (Cube.alphabet s.α n) blocks (cube.h*cube.b) :=
      packet_vertex_card_le_padded _ _ _ _ cube.block_pos
    _ ≤ 2*(5*X) := Nat.mul_le_mul_left 2 pad
    _ ≤ 10*(r*n+1)^2 := by rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_left 10 total
  exact ⟨bounded,bounded.trans_lt words.2.2.1,bounded.trans_lt words.2.2.2.1,bounded.trans_lt words.2.2.2.2⟩

/-- Combine the calibrated global packet bound with the polynomial bound on the
expanded host records. This applies to each numbered path by its actual occurrence
inequality, and leaves the exponent and coefficients independent of the history. -/
theorem JointSchedule.eventually_payload_packet_capacity {K : Type*} [Field K] (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{u} s (E+1) d Q A B j) (C k : ℕ) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      let R := b.physical.teamsPred n+1
      let ξ := (s.τ:ℝ)/5
      let symbols := Cube.alphabet s.α n
      ∀ W : ℝ, W ≤ (R*exterior ξ r n : ℕ) →
        let blocks := blocksFor W (cube.h*cube.b) (symbols^(cube.pred+1))
        ∀ payload count : ℕ, payload ≤ C*(r*n+1)^k →
          count ≤ payload+Fintype.card (Packet cube.pred symbols blocks × Vertex (cube.pred+1)) →
          count ≤ (C+10)*(r*n+1)^(max k 2) ∧ count < 2^b.physical.word n ∧
            count < 2^b.physical.tally n ∧ count < 2^b.physical.multBits n := by
  filter_upwards [b.eventually_packet_occurrences cube,b.eventually_word_capacity (C+10) (max k 2)] with n packet cap
  intro r R ξ symbols W budget blocks payload count host paths
  have grow (k' : ℕ) (hh : k' ≤ max k 2) : (r*n+1)^k' ≤ (r*n+1)^(max k 2) :=
    Nat.pow_le_pow_right (by omega) hh
  have cubeRoom := (packet W budget).1.trans (Nat.mul_le_mul_left 10 (grow 2 (le_max_right ..)))
  have hostRoom := host.trans (Nat.mul_le_mul_left C (grow k (le_max_left ..)))
  have bound := paths.trans (Nat.add_le_add hostRoom cubeRoom)
  rw [← Nat.add_mul] at bound
  exact ⟨bound,bound.trans_lt cap.2.2.1,bound.trans_lt cap.2.2.2.1,bound.trans_lt cap.2.2.2.2⟩

end Diagonal

end BorderVNP
end Computability
end OAI
