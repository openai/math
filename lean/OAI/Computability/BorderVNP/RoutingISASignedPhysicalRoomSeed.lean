import OAI.Computability.BorderVNP.DiagonalCubeSelectedWorkspace
import OAI.Computability.BorderVNP.PackedHistorySeedPlan
import OAI.Computability.BorderVNP.TeamProcessorLiteralScale

/-! # Concrete original-site roster and one-copy sidecar capacity -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter TeamScales Crossing Cover Packing PackedHistoryCircuit.Normalized
open PackedHistoryCircuit.Normalized.SelectedSchedule RoutingISA.CubeArena _root_.OAI.Computability.BorderVNP.Cube.Physical
open scoped Classical BorderVNP.Epoch.Cube
open private log_width from OAI.Computability.BorderVNP.TeamProcessorLiteralScale

private theorem header_word_polynomial {n r : ℕ} (hn : 1≤n) (hr : 1≤r) :
    2^(60*logWidth r n) ≤ (4*(r*n+1))^60 := by
  have pos : 1 < 2*n*r := by
    have h := Nat.mul_le_mul_right (2*n) hr
    rw [one_mul,Nat.mul_comm r (2*n)] at h; omega
  have before := Nat.pow_pred_clog_lt_self (b:=2) (by decide) pos
  have power : 2^Nat.clog 2 (2*n*r) ≤ 4*(r*n+1) := by
    have step : Nat.clog 2 (2*n*r) = Nat.clog 2 (2*n*r)-1+1 := by
      have := Nat.clog_pos (by decide : 1<2) pos; omega
    conv_lhs => rw [step,pow_succ]
    have adjusted : (2:ℕ)^(Nat.clog 2 (2*n*r)-1)<2*n*r := before
    have right : 2*n*r = 2*(r*n) := by ring
    have raw := Nat.mul_le_mul_right 2 adjusted.le
    omega
  rw [log_width,Nat.mul_comm 60,pow_mul]
  exact Nat.pow_le_pow_left power _

universe u
variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {e : PaidIdentity F D m}
    {S : SiteSchedule e} {extra E dlog Q A B j : ℕ}

/-- The public seed's actually installed channel width has a polynomial
ceiling before any private routing choices are made. -/
theorem channel_room_of_seed {a : ℕ} (scales : EpochScales S a extra) {n r header : ℕ}
    (hn : 1≤n) (hr : 1≤r) (seed : Nonempty (SeedPlan S n r (CoverScale.initialDepth (Epoch.Cube D) r n-1)
      (epochs scales.τ n) (TeamScales.width n scales.α) header Q)) :
    DeckGrid.seedChannelWidth n r (Fintype.card (Epoch.Cube D))
        (CoverScale.initialDepth (Epoch.Cube D) r n-1) ≤ (4*(r*n+1))^60 := by
  obtain ⟨plan⟩ := seed
  have copies : 1≤width n scales.α := by
    have real : 1≤(n:ℝ) := by exact_mod_cast hn
    exact Nat.le_floor (by simpa using Real.one_le_rpow real (by exact_mod_cast scales.alpha_pos.le))
  have size := plan.small
  have channel := (Nat.le_mul_of_pos_left _ copies).trans size.le
  exact channel.trans (header_word_polynomial hn hr)

/-- The actual nonempty seed plan supplies the one-copy mark ceiling. This
polynomial estimate uses only its already fitted physical channel and holds
for every original-tile placement and every accepted history. -/
theorem mark_room_of_seed {a : ℕ} (scales : EpochScales S a extra) {n r header : ℕ}
    (hn : 1≤n) (hr : 1≤r) (seed : Nonempty (SeedPlan S n r (CoverScale.initialDepth (Epoch.Cube D) r n-1)
      (epochs scales.τ n) (TeamScales.width n scales.α) header Q)) :
    DeckGrid.seedSiteCapacity n r (Fintype.card (Epoch.Cube D))
        (CoverScale.initialDepth (Epoch.Cube D) r n-1) ≤ 2*(4*(r*n+1))^60 :=
  (DeckGrid.seed_capacity_le n r _ _).2.trans (Nat.mul_le_mul_left 2 (channel_room_of_seed scales hn hr seed))

/-- Primitive bounds for the exact selected cube and the global number of
retained original bundle rows. The geometry end is the real allocated end of
the decoder preceding the cube. -/
theorem JointSchedule.eventually_signed_source_sizes {K : Type*} [Field K] (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{u} s (E+1) dlog Q A B j) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let R := b.physical.teamsPred n+1
      let W := b.physical.word n
      let X := R*exterior ((s.τ:ℝ)/5) r n
      let symbols := Cube.alphabet s.α n
      let start := CoverScale.initialDepth (Epoch.Cube D) r n
      let V := CoverScale.sites (Epoch.Cube D) start
      let T := epochs s.τ n
      let cells := CoverScale.sites (Epoch.Cube D) (EnrichedOuter.depth S start T)
      let cables := (boundary S start T).edges+4*(R*V)
      ∀ (dir : Directory.Layout) (next profile gates outputs width : ℕ),
        let base := GeometryAdvice.Allocation.stop (next+7*dir.candidates) profile gates outputs width W
        base ≤ 2*r*n →
        (selectedSizes base symbols X cells cables dir.candidates R r n profile).Le (4*(r*n+1)^2) ∧
          (epochCopies S)^T*V ≤ r*n+1 := by
  filter_upwards [b.eventually_cube_primitives cube,eventually_compiled_dimensions S s,eventually_ge_atTop 1]
    with n primitive geometry hn
  intro r R W X symbols start V T cells cables dir next profile gates outputs width base baseFit
  have hr := stretch_one b.ρ n
  have bounds := (geometry r hr).2.2.1
  have teams := (b.sizes hn).1
  change R=TeamScales.teams s.α s.τ (S.fanIn^S.rounds) n at teams
  rw [←teams] at bounds
  change routingRows (boundary S start T) cells ((epochCopies S)^T*V) (R*V)≤r*n at bounds
  unfold routingRows CellAddressCircuit.count at bounds
  refine ⟨selectedSizes_bound hr baseFit primitive.2.1 primitive.2.2.2.2.1 (by omega)
    (by dsimp only [cables]; omega) (candidates_le_geometry_stop dir next profile gates outputs width W) primitive.2.2.1,by omega⟩

end Diagonal

end BorderVNP
end Computability
end OAI
