import OAI.Computability.BorderVNP.DiagonalSelectedRouteTable
import OAI.Computability.BorderVNP.DiagonalCubePublicationRoom
import OAI.Computability.BorderVNP.DiagonalExternalSewScale
import OAI.Computability.BorderVNP.PackedDirectoryBits
import OAI.Computability.BorderVNP.PackedTerminalShape

/-! # Physical counts of the signed label and demand scheduler -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Cover Crossing Packing TeamScales Shortening Shortening.PublicCapacity
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {F : Type} [Field F] {e : PaidIdentity F D m}
    {S : PackedHistoryCircuit.Normalized.SiteSchedule e} {extra a E dlog Q A B j : ℕ} {s : EpochScales S a extra}

/-- A constant depending only on the initial deck dimension, accounting for all
initial directed cables, the four sewn cable slots, and every data candidate. -/
noncomputable def signedRowConstant (D : ℕ) := Fintype.card (DeckGrid.Direction (Fintype.card (Epoch.Cube D)))+18

/-- Count the real terminal cells, padded internal and external cable slots, and
every emitted seven-word data row, before and after reading private placements.
The growth and multiplicity are exactly those used by the calibrated window. -/
theorem JointSchedule.eventually_signed_schedule_counts (b : JointSchedule s E dlog Q A B j) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let R := b.physical.teamsPred n+1
      let start := CoverScale.initialDepth (Epoch.Cube D) r n
      let V := CoverScale.sites (Epoch.Cube D) start
      let T := epochs s.τ n
      let M := max ((epochGrowth S extra)^T) R
      let cells := CoverScale.sites (Epoch.Cube D) (EnrichedOuter.depth S start T)
      let cables := (boundary S start T).edges+4*(R*V)
      let J := (epochCopies S)^T*V
      1 ≤ r ∧ 1 ≤ R ∧ R ≤ M ∧ r ≤ V ∧ (V:ℝ) ≤ r*(n:ℝ)^(9/10:ℝ) ∧
      J ≤ R*V ∧ R ≤ Cube.alphabet s.α n ∧ ∀ desc,
        let dir := ExternalSew.freeDirectory (b.physical.teamsPred n) r (literal s.α n) (b.physical.link n)
          V (blockWidth (r*n) V) J desc
        dir.candidates ≤ 8*(R*V) ∧ ∀ pp lp,
        1+cells+cables+(dir.directory pp lp).length ≤ signedRowConstant D*(V+1)*(M+1) := by
  have α0 : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have τ0 : 0 ≤ (s.τ:ℝ) := by exact_mod_cast s.tau_pos.le
  have block := ExternalSew.eventually_block_fields (Epoch.Cube D) α0 s.alpha_small τ0 s.tau_small
    (epochCopies_pos S) s.copy_rate
  filter_upwards [b.eventually_lengths 0,b.eventually_directory_cover,block,
    eventually_compiled_dimensions S s,eventually_ranges S s (fun _ => 0) (fun _ => 0),
    eventually_ge_atTop 1] with n size cover slots dims range hn
  intro r R start V T M cells cables J
  let deg := Fintype.card (DeckGrid.Direction (Fintype.card (Epoch.Cube D)))
  have hr : 1 ≤ r := stretch_one ..
  have hR : 1 ≤ R := Nat.succ_pos _
  have leR : R ≤ M := le_max_right ..
  have vRoom : (V:ℝ) ≤ r*(n:ℝ)^(9/10:ℝ) := size.cover.2.2.2.1
  have original : J ≤ R*V := Nat.mul_le_mul_right V cover.2.2
  have realn : (1:ℝ) ≤ n := by exact_mod_cast hn
  have abc : R ≤ Cube.alphabet s.α n := by
    have grow : (R:ℝ) ≤ (n:ℝ)^(3*(s.α:ℝ)) := size.teams.2.trans
      (Real.rpow_le_rpow_of_exponent_le realn (by linarith))
    exact (Nat.cast_le (α := ℝ)).mp (grow.trans (Nat.le_ceil _))
  refine ⟨hr,hR,leR,cover.1,vRoom,original,abc,?_⟩
  intro desc dir
  have short : literal s.α n ≤ n := Nat.floor_le_of_le (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le realn (show 1-(s.α:ℝ)/3 ≤ 1 by linarith))
  have aligned := slots r hr (r*n) (Nat.mul_pos hr hn) le_rfl
  have count := dir.candidates_le aligned.1 le_rfl ((Nat.mul_le_mul_left r short).trans aligned.2.1) cover.1 original
  refine ⟨count,?_⟩
  intro pp lp
  let old := boundary S start T
  let bot := bottom (D:=D) start
  have rows := epochRows_le e S.positiveFanIn S.rounds (interiors S) V (bins S) (seedCount S start)
    (range r hr).1 bot T
  change old.volume V ≤ (epochRowFactor S)^T*bot.volume V at rows
  have bots : bot.volume V ≤ (deg+3)*(V+1) := by
    change V+V*deg+V+1 ≤ (deg+3)*(V+1)
    nlinarith
  have grow : (epochRowFactor S)^T ≤ M+1 := ((Nat.pow_le_pow_left (epochGrowth_bounds S extra).2.2.2.2.1 T).trans
    (le_max_left _ _)).trans (Nat.le_succ M)
  let sizeBound := (V+1)*(M+1)
  have edges : old.edges ≤ (deg+3)*sizeBound := calc
    old.edges ≤ old.volume V := by unfold Shape.volume; omega
    _ ≤ (epochRowFactor S)^T*bot.volume V := rows
    _ ≤ (M+1)*((deg+3)*(V+1)) := Nat.mul_le_mul grow bots
    _ = (deg+3)*sizeBound := by dsimp only [sizeBound]; ring
  have live : R*V ≤ sizeBound :=
    (Nat.mul_le_mul (Nat.le_succ V) (leR.trans (Nat.le_succ M))).trans' (Nat.mul_comm R V).le
  have atLeast : V+1 ≤ sizeBound := Nat.le_mul_of_pos_right (V+1) (Nat.succ_pos M)
  have cellsLow : cells ≤ V := (dims r hr).1
  have emitted : (dir.directory pp lp).length ≤ 8*(R*V) := (dir.directory_length_le pp lp).trans count
  change 1+cells+(old.edges+4*(R*V))+(dir.directory pp lp).length ≤ (deg+18)*(V+1)*(M+1)
  rw [Nat.mul_assoc (deg+18)]
  change _ ≤ (deg+18)*sizeBound
  nlinarith [Nat.mul_le_mul_left 8 live,Nat.mul_le_mul_left 4 live]

end Diagonal

end BorderVNP
end Computability
end OAI
