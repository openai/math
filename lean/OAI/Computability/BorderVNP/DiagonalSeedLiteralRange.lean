import OAI.Computability.BorderVNP.DiagonalJointSeedStorage

/-! # Physical source capacity of the actual private signed descriptions -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Cover BorderVNP.Epoch Packing Packing.DeckGrid TeamScales Filter ExternalSew
open PackedHistoryCircuit.Normalized

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {a extra E deg Q A B j : ℕ} {s : EpochScales S a extra}

/-- The complete private source matrix fits the shared original literal tails.
These bounds include the true header, padded factor body and report suffix.
Their threshold is uniform over all later private witness and chart choices. -/
theorem JointSchedule.eventually_seedLiteralRanges (b : JointSchedule s E deg Q A B j) (header : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let d := CoverScale.initialDepth (Cube D) r n-1
      let axes := Fintype.card (Cube D)
      let cap := seedBoxCapacity n r axes d (Fintype.card (Direction axes))
      let desc := seedDescriptionWidth n r axes d (header*logWidth r n) (BottomGridBank.bodyBudget cap)
      let entries := (epochCopies S)^epochs s.τ n*GridHosts.tileCount axes d
      let tail := literal s.α n/2
      0 < tail ∧ cap ≤ n ∧ desc ≤ n ∧ desc ≤ tail ∧ entries*desc ≤ (b.physical.teamsPred n+1)*r*tail := by
  filter_upwards [b.eventually_geometricSeedStorage header,eventually_ge_atTop 1] with n storage hn
  intro r d axes cap desc entries tail
  have small : desc ≤ tail := storage.2.2.2.1
  have capBody : cap < BottomGridBank.bodyBudget cap := by
    unfold BottomGridBank.bodyBudget
    exact (show cap < 1+19*cap by omega).trans_le (Nat.le_mul_of_pos_right _ (by omega))
  have capDesc : BottomGridBank.bodyBudget cap ≤ desc := by
    dsimp only [desc,seedDescriptionWidth]
    omega
  have αpos : 0 ≤ (s.α : ℝ) := by exact_mod_cast s.alpha_pos.le
  have lit : literal s.α n ≤ n := Nat.floor_le_of_le
    ((Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1:ℝ) ≤ n)
      (show (1:ℝ)-(s.α:ℝ)/3 ≤ 1 by linarith)).trans_eq (Real.rpow_one _))
  have bound := small.trans ((Nat.div_le_self _ _).trans lit)
  refine ⟨(Nat.zero_le _).trans_lt ((capBody.trans_le capDesc).trans_le small),
    (capBody.le.trans capDesc).trans bound,bound,small,?_⟩
  rw [(b.sizes hn).1]
  exact storage.2.2.2.2

end Diagonal

end BorderVNP
end Computability
end OAI
