import OAI.Computability.BorderVNP.DiagonalJointSeedStorage
import OAI.Computability.BorderVNP.PackedInheritedWorkHorizon
import OAI.Computability.BorderVNP.PackedHistorySeedWord

/-! # Word and rectangle inputs to the width compiler at the chosen processor exponent -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Cover BorderVNP.Epoch Packing DeckGrid Filter TeamScales
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open scoped Classical BorderVNP.Epoch.Cube

universe u
variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {a extra E deg Q A B j : ℕ} {s : EpochScales S a extra}

/-- The actual processor exponent selected for the diagonal argument provides the
public rectangle fits and the horizon-wide word bound for the inherited-width gates. -/
theorem JointSchedule.eventually_inheritedWidthInputs (b : JointSchedule.{u} s E deg Q A B j) (header : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let d := CoverScale.initialDepth (Cube D) r n-1
      let copies := TeamScales.width n s.α
      let T := epochs s.τ n
      let w := 60*logWidth r n
      WidthRanges S (d+1) T w ∧ 2*(S.publicProgramFactor^T*initialMass (D:=D) n r d copies header) < 2^w := by
  filter_upwards [b.eventually_programSeedStorage header,
    eventually_ranges S s (fun _ => 0) (fun _ => 0)] with n stored ranges
  intro r d copies T w
  have hd : d+1 = CoverScale.initialDepth (Cube D) r n := by
    have h : 1 ≤ CoverScale.initialDepth (Cube D) r n := Nat.succ_pos _
    dsimp only [d]; omega
  constructor
  · rw [hd]
    exact WidthRanges.of_ranges S ((ranges r (stretch_one ..)).2)
  · have h : 7*(S.publicProgramFactor^T*initialMass (D:=D) n r d copies header) < 2^w := stored.2.2.1
    omega

end Diagonal

end BorderVNP
end Computability
end OAI
