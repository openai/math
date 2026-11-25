import OAI.Computability.BorderVNP.PackedTerminalEmitterCost
import OAI.Computability.BorderVNP.PackedTerminalRoutingCapacity
import OAI.Computability.BorderVNP.PackedHistoryNormalizedOuter

/-! # Length-only dimensions of the terminal native geometry

The allocated arrays include the entire final product cover and every
reserved old cable and sewn exterior slot. Their dimensions depend only
on the calibrated schedule and the processor count.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover Cover.AddressCircuit BorderVNP.Epoch Packing Shortening Shortening.PublicCapacity Diagonal TeamScales Filter
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
    {a x : ℕ} (scale : EpochScales S a x)

/-- All circuit sizes and numeric widths passed to the full routed-cell
word emitter on the actual final cover. Padding and empty cells are charged
for every branch before any count profile is read. -/
theorem eventually_compiled_dimensions :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r →
      let start := CoverScale.initialDepth (Cube D) r n
      let V := CoverScale.sites (Cube D) start
      let T := epochs scale.τ n
      let d := EnrichedOuter.depth S start T
      let C := CoverScale.sites (Cube D) d
      let A := teams scale.α scale.τ (S.fanIn^S.rounds) n*V
      let J := (S.fanIn^S.rounds)^T*V
      let old := boundary S start T
      let M := old.edges+4*A
      let R := routingRows old C J A
      let W := (360*Fintype.card (Cube D)+60)*logWidth r n
      C≤V ∧ (R:ℝ) ≤ r*(n:ℝ)^(91/100:ℝ) ∧ R≤r*n ∧
        keyWidth (Fintype.card (Cube D)) (d+1)≤W ∧ 60*logWidth r n≤W ∧ Nat.clog 2 R≤W ∧
        ∀ controls extra, 3*M+(RoutingOutputs.count M C J A+((C+(J+C))+(controls+extra))) ≤ 3*R+controls+extra := by
  filter_upwards [eventually_routing_rows S scale,eventually_ge_atTop 1] with n bound hn
  intro r hr start V T d C A J old M R W
  have smaller : d+1 ≤ start+1 := by dsimp only [d,EnrichedOuter.depth]; omega
  have cells : C≤V := tiles_mono (Cube D) smaller
  have rows : (R:ℝ) ≤ r*(n:ℝ)^(91/100:ℝ) := bound r hr C cells
  have small : R≤r*n := by
    apply (Nat.cast_le (α:=ℝ)).mp
    rw [Nat.cast_mul,← Real.rpow_one (n:ℝ)]
    exact rows.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : 1≤(n:ℝ)) (by norm_num)) (Nat.cast_nonneg r))
  have allocated : 1+CellAddressCircuit.count old.sites M A C+J+A ≤ R := le_rfl
  have inRows : C≤R := by unfold CellAddressCircuit.count at allocated; omega
  have words := TerminalCells.sorting_width (Cube D) hr hn (d:=d) inRows small
  exact ⟨cells,rows,small,words.1,words.2.1,words.2.2,fun _ _ => TerminalCells.output_count allocated⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
