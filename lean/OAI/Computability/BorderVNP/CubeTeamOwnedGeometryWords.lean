import OAI.Computability.BorderVNP.CubeLabelResources
import OAI.Computability.BorderVNP.TransmissionDataKeys

/-! # Word room for the real intercell traffic and the checked group thresholds -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.LabelIndex

open TeamScales Filter

/-- Both scaled capacity thresholds and the label optimizer's full score envelope
fit the paper's word width. The incoming literal rows and the crossing wires use
the same processor count and the same exterior scale. -/
theorem eventually_publication_words {α ξ : ℝ} (hα : 0 < α) (a : ℕ) (small : α*a < 1/10^6)
    (nonneg : 0 ≤ ξ) (gap : ξ < α/3) :
    ∀ᶠ k : ℕ in atTop, ∀ (D : Packing.Directory.Layout) (w wires : ℕ),
      let X := exterior ξ D.processors k
      D.DestinationBounds → D.literal = literal α k → D.teams ≤ k → logWidth D.processors k^2 ≤ w →
      wires ≤ 2*D.teams*X →
      1000000 < 2^w ∧ 1000000*X*D.teams < 2^w ∧
        wordEnvelope (labelCount α a k) (wires+D.teams*((D.fields+1)*(D.processors*D.literal))) < 2^w := by
  filter_upwards [eventually_envelope hα a small nonneg 1000000 0, eventually_literals_le gap 3] with k room lanes
  intro D w wires X bounds lit teamCount wide cables
  let maxVolume := 1000000*(X*D.teams+1)
  have fit : wordEnvelope (labelCount α a k) maxVolume < 2^w := by
    simpa only [Nat.zero_add] using room D.processors D.teams w 0 maxVolume bounds.processors teamCount wide
      (Nat.zero_le _) le_rfl
  have few : D.fields+1 ≤ 3 := by have := bounds.fields; omega
  have data : (D.fields+1)*(D.processors*D.literal) ≤ X :=
    (Nat.mul_le_mul_right _ few).trans (by simpa only [←Nat.mul_assoc,lit] using lanes D.processors)
  have widthBound : wires+D.teams*((D.fields+1)*(D.processors*D.literal)) ≤ maxVolume := by
    have h := Nat.mul_le_mul_left D.teams data
    have hc : wires ≤ 2*(X*D.teams) := by simpa only [Nat.mul_assoc,Nat.mul_comm D.teams X] using cables
    rw [Nat.mul_comm D.teams X] at h
    dsimp only [maxVolume]
    omega
  have less : maxVolume ≤ wordEnvelope (labelCount α a k) maxVolume := by
    unfold wordEnvelope
    have base : maxVolume ≤ (maxVolume+1)^2 := (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
    have pos : 0 < (labelCount α a k+1)^6 := pow_pos (by omega) _
    exact base.trans ((Nat.le_mul_of_pos_left _ (by decide : 0 < 4)).trans (Nat.le_mul_of_pos_right _ pos))
  have limit := less.trans_lt fit
  refine ⟨?_,?_,lt_of_le_of_lt ?_ fit⟩
  · dsimp only [maxVolume] at limit
    omega
  · dsimp only [maxVolume] at limit
    rw [Nat.mul_assoc]
    omega
  · unfold wordEnvelope
    gcongr

end Cube.LabelIndex

end BorderVNP
end Computability
end OAI
