import OAI.Computability.BorderVNP.DiagonalSignedDescriptionFits

/-! # The complete original-description interval inside an actually selected signed cell bank -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Cover Epoch TeamScales Packing DeckGrid Inherited Filter ExternalSew
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {a extra E deg Q A B j : ℕ} {s : EpochScales S a extra}

/-- The actual stride pays for the supplied lanes, the signed report gap and
all one-copy original descriptions. The estimate is uniform over the later
choice of owner map, so also applies to the specific reached cells. -/
theorem JointSchedule.eventually_signed_original_bank (b : JointSchedule s E deg Q A B j) (header : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let d := CoverScale.initialDepth (Cube D) r n-1
      let T := epochs s.τ n
      let axes := Fintype.card (Cube D)
      let tiles := GridHosts.tileCount axes d
      let J := (epochCopies S)^T*tiles
      let B₀ := initialMass (D:=D) n r d (width n s.α) header
      let cap := 15*(S.publicProgramFactor^T*B₀)
      let bytes := seedDescriptionWidth n r axes d (header*logWidth r n)
        (BottomGridBank.bodyBudget (seedBoxCapacity n r axes d (Fintype.card (Direction axes))))
      ∀ {C : ℕ} (owner : Fin J → Fin C) (c : Fin C) (gap supplied : ℕ),
        gap ≤ n^2 → supplied ≤ cap →
          supplied+gap+(∑ j, if owner j=c then bytes else 0) ≤ 3*(r*n)^2+1 := by
  filter_upwards [b.eventually_programSeedStorage header,b.eventually_lengths 0,eventually_ge_atTop 15] with n stored geom hn
  intro r d T axes tiles J B₀ cap bytes C owner c gap supplied hg hsup
  have pos : 1≤n := by omega
  have hr : 1≤r := stretch_one ..
  have rn : n≤r*n := Nat.le_mul_of_pos_left n hr
  have exponent : 2*(s.α:ℝ)≤1 := by linarith [s.alpha_small]
  have num : b.physical.teamsPred n+1 ≤ n := by
    exact_mod_cast geom.teams.2.trans ((Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast pos) exponent).trans_eq (Real.rpow_one _))
  have teams : width n s.α * (epochCopies S)^T ≤ n := by
    rw [(b.sizes pos).1] at num
    exact num
  have hn1 : 1≤(n:ℝ) := by exact_mod_cast pos
  have one : width n (1/5:ℝ) ≤ n := Nat.floor_le_of_le
    ((Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1/5:ℝ) ≤ 1)).trans_eq (Real.rpow_one _))
  have alpha : 0≤(s.α:ℝ) := by exact_mod_cast s.alpha_pos.le
  have ls : literal s.α n ≤ n := Nat.floor_le_of_le
    ((Real.rpow_le_rpow_of_exponent_le hn1 (by linarith : 1-(s.α:ℝ)/3 ≤ 1)).trans_eq (Real.rpow_one _))
  have paid : J*bytes ≤ width n s.α*(epochCopies S)^T*r*(literal s.α n/2) := stored.2.2.2.2
  have tot : J*bytes ≤ (r*n)^2 := by
    calc
      _ ≤ n*r*n := paid.trans (Nat.mul_le_mul (Nat.mul_le_mul_right r teams) ((Nat.div_le_self _ _).trans ls))
      _ ≤ _ := by rw [Nat.mul_comm n r,pow_two]; exact Nat.mul_le_mul_left _ rn
  have upto : (∑ j, if owner j=c then bytes else 0) ≤ J*bytes := by
    calc
      _ ≤ ∑ _ : Fin J, bytes := Finset.sum_le_sum fun i _ => by split <;> simp
      _ = J*bytes := by simp
  have measured : 7*(S.publicProgramFactor^T*B₀) ≤ width n (1/5:ℝ) := stored.2.1
  have bb : S.publicProgramFactor^T*B₀ ≤ n := by omega
  have leak : supplied ≤ (r*n)^2 := hsup.trans <| (Nat.mul_le_mul (hn.trans rn) (bb.trans rn)).trans_eq (pow_two _).symm
  exact (Nat.add_le_add (Nat.add_le_add leak (hg.trans (Nat.pow_le_pow_left rn 2))) (upto.trans tot)).trans (by omega)

end Diagonal

end BorderVNP
end Computability
end OAI
