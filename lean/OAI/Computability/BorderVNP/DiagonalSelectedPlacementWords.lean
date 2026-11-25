import OAI.Computability.BorderVNP.DiagonalCubePublicationRoom
import OAI.Computability.BorderVNP.DiagonalExternalFreeGroups
import OAI.Computability.BorderVNP.DiagonalCubeStartupWorkspace

/-! # Seven-word directory placement and the complete selected cell stride -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter TeamScales Crossing Cover Packing PackedHistoryCircuit.Normalized
open PackedHistoryCircuit.Normalized.SelectedSchedule RoutingISA RoutingISA.CubeArena ExternalSew
open Packing.RoutingOutputs
open scoped Classical BorderVNP.Epoch.Cube

universe u
variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {e : PaidIdentity F D m}
    {S : SiteSchedule e} {a extra E dlog Q A B j : ℕ} {s : EpochScales S a extra}

/-- The placement writer can scan the whole actual stride, including its final sentinel.
The receiving and live pointer bases are the physical positions in the gate program's
packet. The estimate is simultaneous in the later private row width and all cell ranks. -/
theorem JointSchedule.eventually_selected_placement_words (b : JointSchedule.{u} s (E+1) dlog Q A B j) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let R := b.physical.teamsPred n
      let w := b.physical.word n
      let V := CoverScale.sites (Epoch.Cube D) (CoverScale.initialDepth (Epoch.Cube D) r n)
      let entries := (epochCopies S)^(epochs s.τ n)*V
      ∀ (desc next profile gates outputs field cables cells : ℕ),
        let dir := freeDirectory R r (literal s.α n) (b.physical.link n) V (blockWidth (r*n) V) entries desc
        let fresh := next+7*dir.candidates
        let origin := GeometryAdvice.Allocation.dest fresh profile gates outputs field
        let base := GeometryAdvice.Allocation.stop fresh profile gates outputs field w
        let tabs := bases origin cables cells entries
        desc ≤ n → base ≤ 2*r*n →
        cables*3+RoutingOutputs.count cables cells entries (dir.teams*V)+(cells+(entries+cells)+37) ≤ outputs →
        ∀ extent ≤ 3*(r*n)^2+1,
          Directory.ISA.wordBound (Directory.ISA.placementBound dir tabs.privatePairs tabs.livePairs extent) < 2^w := by
  filter_upwards [b.eventually_directory_cover,b.eventually_word_capacity (32*32^4) 8,
    eventually_ge_atTop 1] with n cover space hn
  intro r R w V entries desc next profile gates outputs field cables cells dir fresh origin base tabs descFit baseFit output extent cap
  let U := r*n
  let Z := U+1
  have hr : 0 < r := stretch_one ..
  have nz : n ≤ U := Nat.le_mul_of_pos_left _ hr
  have Upos : 0 < U := Nat.mul_pos hr hn
  have Vpos := hr.trans_le cover.1
  have candidates : dir.candidates ≤ 2*U := by
    simpa only [U,Nat.mul_assoc] using (candidates_le_geometry_stop dir next profile gates outputs field w).trans baseFit
  have αpos : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have lit : dir.literal ≤ n := Nat.floor_le_of_le
    ((Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1:ℝ) ≤ n)
      (show (1:ℝ)-(s.α:ℝ)/3 ≤ 1 by linarith)).trans_eq (Real.rpow_one _))
  let ξ := (s.τ:ℝ)/5
  have ξpos : 0 ≤ ξ := by dsimp only [ξ]; exact div_nonneg (by exact_mod_cast s.tau_pos.le) (by norm_num)
  have bound := exterior_links_le ξ dir.teams n
  have linkEq : dir.link = TeamScales.link ξ dir.teams n := by
    change b.physical.link n = TeamScales.link ξ (R+1) n
    rw [(b.sizes hn).2.1,← (b.sizes hn).1]
  have peers : (dir.teams-1)*dir.link ≤ n := by
    rw [linkEq]
    exact bound.trans (Nat.floor_le_of_le ((Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1:ℝ) ≤ n)
      (show 1-ξ ≤ 1 by linarith)).trans_eq (Real.rpow_one _)))
  have block : dir.block ≤ U := (ceilDiv_le_iff_le_mul Vpos).mpr (Nat.le_mul_of_pos_left _ Vpos)
  have site : dir.sites ≤ U := cover.2.1
  have stride : dir.stride ≤ 3*U := by
    change 2*dir.literal+(dir.teams-1)*dir.link ≤ 3*U
    omega
  have whole : controlsBase origin cables cells entries (dir.teams*V)+37 ≤ base := by
    dsimp only [controlsBase,bases,RoutingOutputs.count] at output ⊢
    change _ ≤ origin+outputs+GeometryOutput.packetCount profile gates outputs field*w+GeometryOutput.packetCount profile gates outputs field
    omega
  have tableFit : tabs.privatePairs ≤ 2*U ∧ tabs.livePairs ≤ 2*U := by
    dsimp only [tabs,controlsBase,bases] at whole ⊢
    have top : base ≤ 2*U := by simpa only [U,Nat.mul_assoc] using baseFit
    omega
  have un : U ≤ Z^2 := by
    rw [pow_two]
    exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have larger : U^2 ≤ Z^2 := Nat.pow_le_pow_left (Nat.le_succ U) _
  have one : 1 ≤ Z^2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have descFit₀ : dir.description ≤ n := descFit
  change extent ≤ 3*U^2+1 at cap
  have p : Directory.ISA.placementBound dir tabs.privatePairs tabs.livePairs extent+1 ≤ 32*Z^2 := by
    dsimp only [Directory.ISA.placementBound]
    omega
  change 32*(Directory.ISA.placementBound dir tabs.privatePairs tabs.livePairs extent+1)^4 < 2^w
  calc
    _ ≤ 32*(32*Z^2)^4 := Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left p 4)
    _ = (32*32^4)*Z^8 := by ring
    _ < _ := space.2.2.1

end Diagonal

end BorderVNP
end Computability
end OAI
