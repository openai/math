import OAI.Computability.BorderVNP.DiagonalCubePrimitiveScales
import OAI.Computability.BorderVNP.RoutingISACubeSelectedRoom
import OAI.Computability.BorderVNP.PackedRoutingWorkspace

/-! # The selected native cube allocation on the real rounded terminal arrays -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open GeometryAdvice

/-- The demand stream is reserved before the geometry packet. Its candidate
count therefore fits the already checked geometry end, including empty rows. -/
theorem candidates_le_geometry_stop (dir : Packing.Directory.Layout) (next profile gates outputs width w : ℕ) :
    dir.candidates ≤ Allocation.stop (next+7*dir.candidates) profile gates outputs width w := by
  dsimp only [Allocation.stop,Allocation.packed,Allocation.dense,Allocation.dest,Allocation.temp]
  omega

/-- Primitive arrays of the concrete arena. The native router has one possible
row per candidate and one per strict symbol pair. The cell stride covers all
supplied bits, the report interval and the opaque descriptions. -/
def selectedSizes (base symbols traffic cells cables candidates teams r n profile : ℕ) : Sizes :=
  ⟨base,symbols,traffic,cells,cables,candidates+symbols.choose 2,teams,3*(r*n)^2+1,profile⟩

theorem selectedSizes_bound {base symbols traffic cells cables candidates teams r n profile : ℕ}
    (hr : 1 ≤ r) (baseFit : base ≤ 2*r*n) (sy : symbols ≤ n) (volume : traffic ≤ (r*n+1)^2)
    (cs : cells ≤ r*n) (es : cables ≤ r*n) (cand : candidates ≤ base) (team : teams ≤ n) :
    (selectedSizes base symbols traffic cells cables candidates teams r n profile).Le (4*(r*n+1)^2) := by
  have rn : n ≤ r*n := Nat.le_mul_of_pos_left _ hr
  have sq : r*n ≤ (r*n+1)^2 := (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  have pair : symbols.choose 2 ≤ (r*n+1)^2 := by
    rw [Nat.choose_two_right,pow_two]
    apply (Nat.div_le_self _ _).trans
    exact Nat.mul_le_mul ((sy.trans rn).trans (Nat.le_succ _)) ((Nat.sub_le symbols 1).trans ((sy.trans rn).trans (Nat.le_succ _)))
  have stride : (r*n)^2 ≤ (r*n+1)^2 := Nat.pow_le_pow_left (Nat.le_succ (r*n)) 2
  have pos : 1 ≤ (r*n+1)^2 := Nat.pow_pos (Nat.succ_pos _)
  dsimp only [selectedSizes,Sizes.Le]
  rw [Nat.mul_assoc] at baseFit
  omega

end RoutingISA.CubeArena

namespace Diagonal

open Filter TeamScales Crossing Cover Packing PackedHistoryCircuit.Normalized
open PackedHistoryCircuit.Normalized.SelectedSchedule RoutingISA.CubeArena _root_.OAI.Computability.BorderVNP.Cube.Physical
open scoped Classical BorderVNP.Epoch.Cube

universe u
variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {e : PaidIdentity F D m}
    {S : SiteSchedule e} {extra E dlog Q A B j : ℕ}

set_option maxRecDepth 4000 in
/-- On the actual terminal cell and cable counts, one address word accommodates
the entire selected arena. The only placement input is the end of the concrete
geometry workspace, bounded by the selected cover workspace theorem. The row
extent covers the true compact directory for every placement. -/
theorem JointSchedule.eventually_selected_cube_workspace {K : Type*} [Field K] (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{u} s (E+1) dlog Q A B j) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let R := b.physical.teamsPred n+1
      let w := b.physical.word n
      let X := R*exterior ((s.τ:ℝ)/5) r n
      let symbols := Cube.alphabet s.α n
      let start := CoverScale.initialDepth (Epoch.Cube D) r n
      let V := CoverScale.sites (Epoch.Cube D) start
      let T := epochs s.τ n
      let cells := CoverScale.sites (Epoch.Cube D) (EnrichedOuter.depth S start T)
      let cables := (boundary S start T).edges+4*(R*V)
      ∀ (dir : Directory.Layout) (next profile gates outputs width : ℕ),
        let base := GeometryAdvice.Allocation.stop (next+7*dir.candidates) profile gates outputs width w
        base ≤ 2*r*n →
        let sizes := selectedSizes base symbols X cells cables dir.candidates R r n profile
        let arena := sizes.selected cube.pred cube.b cube.h cube.copies cube.width
        0 < arena.header.d ∧ 0 < arena.header.blocks ∧ 1000000 < 2^w ∧ 1000000*X < 2^w ∧
          arena.stop < 2^w ∧ ∀ pp lp, (dir.directory pp lp).length+symbols.choose 2 ≤ arena.maxRows := by
  filter_upwards [b.eventually_cube_primitives cube,eventually_compiled_dimensions S s,
    eventually_selected_word cube.pred cube.b cube.h cube.copies cube.width 4 2 E,eventually_ge_atTop 1]
    with n scalars geometry selected hn
  intro r R w X symbols start V T cells cables dir next profile gates outputs width base baseFit sizes arena
  have hr := stretch_one b.ρ n
  have bounds := geometry r hr
  have small := bounds.2.2.1
  have teams := (b.sizes hn).1
  change R = TeamScales.teams s.α s.τ (S.fanIn^S.rounds) n at teams
  rw [← teams] at small
  change routingRows (boundary S start T) cells ((S.fanIn^S.rounds)^T*V) (R*V) ≤ r*n at small
  unfold routingRows CellAddressCircuit.count at small
  have cellFit : cells ≤ r*n := by omega
  have cableFit : cables ≤ r*n := by dsimp only [cables]; omega
  have tuple : sizes.Le (4*(r*n+1)^2) :=
    selectedSizes_bound hr baseFit scalars.2.1 scalars.2.2.2.2.1 cellFit cableFit
      (candidates_le_geometry_stop dir next profile gates outputs width w) scalars.2.2.1
  refine ⟨scalars.1,scalars.2.2.2.2.2.1,scalars.2.2.2.2.2.2.1,scalars.2.2.2.2.2.2.2,
    ?_,fun pp lp => Nat.add_le_add_right (dir.directory_length_le pp lp) _⟩
  exact selected r sizes hr tuple

end Diagonal

end BorderVNP
end Computability
end OAI
