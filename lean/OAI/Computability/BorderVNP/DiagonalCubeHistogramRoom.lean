import OAI.Computability.BorderVNP.DiagonalCubeSelectedWorkspace

/-! # Word room for every candidate histogram on the selected geometry -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter TeamScales Crossing Cover Packing PackedHistoryCircuit.Normalized
open PackedHistoryCircuit.Normalized.SelectedSchedule RoutingISA.CubeArena _root_.OAI.Computability.BorderVNP.Cube.Physical
open scoped Classical BorderVNP.Epoch.Cube

universe u
variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {e : PaidIdentity F D m}
    {S : SiteSchedule e} {extra E dlog Q A B j : ℕ}

set_option maxRecDepth 4000 in
/-- Uniform accumulator room for all raw in-range declarations, including candidates that the
capacity or subsequent row checks reject. The independent data budget is the three live source
fields of the literal directory. -/
theorem JointSchedule.eventually_selected_histogram_room {K : Type*} [Field K] (cube : FixedCube K)
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
        1000000*(arena.stop+3*R*(r*n))+2*arena.stop < 2^w := by
  obtain ⟨e,fit⟩ := uniform_exponent cube.pred cube.b cube.h cube.copies cube.width
  let degree := max (2*e) 2
  let factor := 1000002*6^e+3000000
  filter_upwards [b.eventually_cube_primitives cube,eventually_compiled_dimensions S s,
    b.eventually_word_capacity factor degree,eventually_ge_atTop 1] with n scalars geometry words hn
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
  let z := r*n+1
  have zz : 1 ≤ z^2 := Nat.one_le_pow _ _ (by omega)
  have six : 4*z^2+2 ≤ 6*z^2 := by omega
  have ar : arena.stop ≤ 6^e*z^(2*e) := by
    have p := (fit _ sizes tuple).trans (Nat.pow_le_pow_left six e)
    simpa only [mul_pow,← pow_mul] using p
  have roomE : z^(2*e) ≤ z^degree := Nat.pow_le_pow_right (by dsimp only [z]; omega) (le_max_left ..)
  have roomD : z^2 ≤ z^degree := Nat.pow_le_pow_right (by dsimp only [z]; omega) (le_max_right ..)
  have rb : R ≤ z := (scalars.2.2.1).trans ((Nat.le_mul_of_pos_left _ hr).trans (Nat.le_succ _))
  have product : R*(r*n) ≤ z^2 := by rw [pow_two]; exact Nat.mul_le_mul rb (Nat.le_succ _)
  have stop := ar.trans (Nat.mul_le_mul_left _ roomE)
  have data := product.trans roomD
  apply lt_of_le_of_lt _ words.2.2.1
  dsimp only [factor]
  rw [Nat.add_mul]
  calc
    _ = 1000002*arena.stop+3000000*(R*(r*n)) := by ring
    _ ≤ 1000002*(6^e*z^degree)+3000000*z^degree := Nat.add_le_add (Nat.mul_le_mul_left _ stop) (Nat.mul_le_mul_left _ data)
    _ = _ := by ring

end Diagonal

end BorderVNP
end Computability
end OAI
