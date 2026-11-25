import OAI.Hierarchy.TaggedWireLinearRoleRoom
import OAI.Hierarchy.TaggedWidePoolPrice

namespace OAI
/-! # Finite signed-role storage appended after the paid calendar and its scratch rows -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom
open ReportSockets TaggedShorterSupergroups ProtocolRAM Filter

private theorem ceiling_shift (z : Sizes) (start : ℕ) : z.ceiling start=3*start+z.ceiling 0 := by
  dsimp [Sizes.ceiling,Sizes.stop,Sizes.offset,Sizes.positive,Sizes.axis,Sizes.ext,Sizes.free,Sizes.pub]
  omega

/-- The genuine high pages can follow arbitrary scratch from the actual paid
program. Their incremental address cost is linear in the number of original
rows, uniformly before the height or the permutation is chosen. -/
theorem appended (S : PurchaseSampler) (W k attempts pad depth : ℕ) (ok : 2*copies k attempts≤2^pad) :
    ∃ C : ℕ,∀ (h R : ℕ) (_order : Fin R≃Edges S h (2^W) k) (start : ℕ),
      let dir:=stageDir h W (copies k attempts) pad ok
      let edges:=R+attempts*(PurchaseFrozen.count h (2^W) k*PurchaseFrozen.paths h S.degree depth)
      (shape (R:=R) S dir edges).ceiling start≤3*start+C*2^h := by
  obtain ⟨C,cap⟩:=linear S W k attempts pad depth 0 ok
  refine ⟨C,?_⟩
  intro h R order start
  dsimp only
  rw [ceiling_shift]
  exact Nat.add_le_add_left (cap h R order 0 (Nat.zero_le _)) _

/-- The physical input and the entire resulting directory fit one native word
when the paid scratch extent is the number of inputs times a polynomial in
the logarithm of that number. -/
theorem appended_word_room (S : PurchaseSampler) (W k attempts pad depth : ℕ)
    (ok : 2*copies k attempts≤2^pad) (B a : ℝ) (ha : 0≤a) :
    ∃ bound : ℝ,∀ᶠ h : ℕ in atTop,∀ (R : ℕ) (_order : Fin R≃Edges S h (2^W) k) (start : ℕ),
      (start:ℝ)≤(2:ℝ)^h*(B*(2*(h:ℝ))^a) →
      let dir:=stageDir h W (copies k attempts) pad ok
      let edges:=R+attempts*(PurchaseFrozen.count h (2^W) k*PurchaseFrozen.paths h S.degree depth)
      let endAt:=(shape (R:=R) S dir edges).ceiling start
      (endAt:ℝ)≤(2:ℝ)^h*(bound*(2*(h:ℝ))^a) ∧ endAt<2^(Native.wordBits h (2^W) Native.copies) := by
  obtain ⟨C,cap⟩:=appended S W k attempts pad depth ok
  refine ⟨3*B+C,?_⟩
  filter_upwards [Tagged.eventually_word_room (3*B+C) a ha,eventually_ge_atTop 1] with h room high
  intro R order start prefixCost
  let dir:=stageDir h W (copies k attempts) pad ok
  let edges:=R+attempts*(PurchaseFrozen.count h (2^W) k*PurchaseFrozen.paths h S.degree depth)
  let endAt:=(shape (R:=R) S dir edges).ceiling start
  have integer : endAt≤3*start+C*2^h:=cap h R order start
  have realBound : (endAt:ℝ)≤3*start+C*(2:ℝ)^h := by exact_mod_cast integer
  have hpos : (1:ℝ)≤h := by exact_mod_cast high
  have power : 1≤(2*(h:ℝ))^a := Real.one_le_rpow (by linarith) ha
  have extra := mul_le_mul_of_nonneg_left power (show 0≤(C:ℝ)*(2:ℝ)^h by positivity)
  have total : (endAt:ℝ)≤(2:ℝ)^h*((3*B+C)*(2*(h:ℝ))^a) := by
    calc
      _ ≤ 3*((2:ℝ)^h*(B*(2*(h:ℝ))^a))+((C:ℝ)*(2:ℝ)^h)*(2*(h:ℝ))^a := by linarith
      _ = _ := by ring
  refine ⟨total,(room endAt total).trans_le (Nat.pow_le_pow_right (by decide) ?_)⟩
  rw [Native.wordBits_linear]
  omega

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom

end
end OAI
