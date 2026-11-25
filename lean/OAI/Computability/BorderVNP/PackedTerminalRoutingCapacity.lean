import OAI.Computability.BorderVNP.PackedHistoryScheduleBudget
import OAI.Computability.BorderVNP.PackedCellAddressCircuit

/-! # Size of the final cable, placement and cell address directories

The rectangular terminal history and the four exterior cable slots per
team and original tile are both charged. The original bottom descriptions
are counted once per bundle, and the final cell catalog is bounded by the
initial deck cover. These are bounds on the actual padded field arrays.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover BorderVNP.Epoch Packing Shortening PublicCapacity Diagonal TeamScales Filter
open scoped Classical

/-- All rows charged by the routing output compiler, including the padded
exterior intervals, original bundles and receiving group slots. -/
def routingRows (s : Shape) (cells original live : ℕ) : ℕ :=
  1+CellAddressCircuit.count s.sites (s.edges+4*live) live cells+original+live

/-- The three occurrences of an old edge come from the cable table and
its two ends. Four slots per team/tile bound the grouped exterior widths. -/
theorem routingRows_le (s : Shape) {C tiles original live : ℕ}
    (cells : C ≤ tiles) (bundles : original ≤ live) :
    routingRows s C original live ≤ 3*s.volume tiles+15*live := by
  unfold routingRows CellAddressCircuit.count Shape.volume; omega

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

/-- Uniform bound on the actual final arrays of the selected geometric schedule.
It includes empty cells, old cable holes, exterior holes, and the one-copy
private description rows behind the final receiving blocks. -/
theorem eventually_routing_rows {a x : ℕ} (scale : EpochScales S a x) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r →
      let start := CoverScale.initialDepth (Cube D) r n
      let tiles := CoverScale.sites (Cube D) start
      let T := epochs scale.τ n
      let fan := S.fanIn^S.rounds
      let live := teams scale.α scale.τ fan n*tiles
      ∀ C ≤ tiles, (routingRows (boundary S start T) C (fan^T*tiles) live : ℝ) ≤ r*(n:ℝ)^(91/100:ℝ) := by
  let dirs := Fintype.card (DeckGrid.Direction (Fintype.card (Cube D)))
  let A : ℝ := dirs+3
  let g := PublicCapacity.epochFactor e S.fanIn S.rounds (interiors S) (bins S)
  have hg : 1 ≤ g := epochFactor_pos e S.positiveFanIn _ _ _
  have ht : 0 ≤ (scale.τ:ℝ) := by exact_mod_cast scale.tau_pos.le
  have hα : 0 ≤ (scale.α:ℝ) := by exact_mod_cast scale.alpha_pos.le
  have rate := scale.rate hg (epochGrowth_bounds S x).2.2.2.2.1
  have fan := epochCopies_pos S
  have copies := scale.rate fan (epochGrowth_bounds S x).2.1
  have gap := eventually_rpow_gap (show 2*(scale.α:ℝ)+(9/10:ℝ)<91/100 by linarith [scale.alpha_small]) (18*A)
  filter_upwards [eventually_grid_volume (Cube D) dirs,eventually_ranges S scale (fun _ => 0) (fun _ => 0),
    gap,eventually_ge_atTop 1] with n initial range absorb hn
  intro r hr start tiles T f live C hC
  let bot := bottom (D:=D) start
  have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have pos := zero_lt_one.trans_le hn'
  have low : (bot.volume tiles : ℝ) ≤ A*(r*(n:ℝ)^(9/10:ℝ)) := initial r hr
  have tileCap : (tiles:ℝ) ≤ A*(r*(n:ℝ)^(9/10:ℝ)) := by
    apply le_trans _ low; exact_mod_cast (show tiles ≤ bot.volume tiles by unfold Shape.volume; omega)
  have hrow := epochRows_le e S.positiveFanIn S.rounds (interiors S) tiles (bins S)
    (seedCount S start) (range r hr).1 bot T
  have grow : ((g^T:ℕ):ℝ) ≤ (n:ℝ)^(2*(scale.α:ℝ)) := by
    push_cast
    apply (epoch_growth_le (by exact_mod_cast hg : 1 ≤ (g:ℝ)) hn ht rate).trans
    exact Real.rpow_le_rpow_of_exponent_le hn' (by linarith)
  have ts : (teams scale.α scale.τ f n:ℝ) ≤ (n:ℝ)^(2*(scale.α:ℝ)) :=
    teams_le fan hn ht (copies.trans (by linarith))
  have atLeast : 1 ≤ width n scale.α := Nat.le_floor (by simpa using Real.one_le_rpow hn' hα)
  have count : f^T*tiles ≤ live := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ atLeast)
  have raw := routingRows_le (boundary S start T) hC count
  have bc : ((boundary S start T).volume tiles:ℝ) ≤ ((g^T:ℕ):ℝ)*bot.volume tiles := by exact_mod_cast hrow
  calc
    _ ≤ 3*((boundary S start T).volume tiles:ℝ)+15*(live:ℝ) := by exact_mod_cast raw
    _ ≤ 3*((n:ℝ)^(2*(scale.α:ℝ))*(A*(r*(n:ℝ)^(9/10:ℝ))))+
        15*((n:ℝ)^(2*(scale.α:ℝ))*(A*(r*(n:ℝ)^(9/10:ℝ)))) := by
      apply add_le_add (mul_le_mul_of_nonneg_left (bc.trans (mul_le_mul grow low (by positivity) (by positivity))) (by norm_num))
      dsimp only [live]; push_cast
      exact mul_le_mul_of_nonneg_left (mul_le_mul ts tileCap (by positivity) (by positivity)) (by norm_num)
    _ = r*(18*A*(n:ℝ)^(2*(scale.α:ℝ)+(9/10:ℝ))) := by rw [Real.rpow_add pos]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left absorb (by positivity)

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
