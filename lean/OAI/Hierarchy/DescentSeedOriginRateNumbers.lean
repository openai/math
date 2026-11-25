import OAI.Hierarchy.DescentSeedEpochRoom
import OAI.Hierarchy.DescentResetWalshScaleNumbers
import OAI.Hierarchy.DescentOperandWidth

namespace OAI
/-! # Cofinal widths of the original selector, original operand and first Walsh row -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
variable {F : Type} [Field F] (G : PoweredGadget F)

theorem first_native_widths (t f g reset drift D K τ B : ℕ) (positive : 0 < B) :
    ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B)
      ∀ M p degree s : ℕ,let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let m:=S.groupWidth k (tail τ J) 0+k
      p ≤ h → degree ≤ D → s ≤ h →
      DescentOperandWidth.recordBits G S k (tail τ J) drift degree p ≤ scale J 3 ∧
      s.log2+1 ≤ scale J 2 ∧ S.localWalshBits p m f K ≤ scale J 3 :=by
  let C:=localCoefficient G t f g reset K τ
  let limit:=max (2*B) (C*(2*B)^2)
  filter_upwards [DescentOperandWidth.issued G drift D t f g reset τ B positive,
    eventually_late limit B positive] with h operands late
  let J:=Nat.log 2 h/(2*B)
  dsimp only
  intro M p degree s pw dw sw
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  have one : J ≤ scale J 1 :=(Nat.le_succ _).trans (by
    simpa only [scale,one_mul] using (Nat.lt_two_pow_self (n:=J+1)).le)
  have c₁ : 2*B ≤ scale J 1 :=(Nat.le_max_left ..).trans (late.trans one)
  have c₂ : C*(2*B)^2 ≤ scale J 1 :=(Nat.le_max_right ..).trans (late.trans one)
  have logh:=log_epoch h B positive
  have jl : J ≤ Nat.log 2 h:=Nat.div_le_self ..
  have tl : tail τ J ≤ τ*(Nat.log 2 h+1)^2 :=by
    apply Nat.mul_le_mul_left
    have sq:=Nat.le_self_pow (by decide : 2≠0) (Nat.log 2 h+1)
    omega
  have wal:=actual_width G t J f g reset M (tail τ J) 0 h p K τ pw jl tl (Nat.zero_le _)
  refine ⟨operands M p degree pw dw,?_,?_⟩
  · rw [Nat.log2_eq_log_two]
    exact ((Nat.succ_le_succ (Nat.log_mono_right (b:=2) sw)).trans logh).trans
      ((Nat.mul_le_mul_right (scale J 1) c₁).trans_eq (scale_mul J 1 1))
  · apply wal.trans
    calc
      C*(Nat.log 2 h+1)^2 ≤ C*((2*B)*scale J 1)^2 :=Nat.mul_le_mul_left _ (Nat.pow_le_pow_left logh _)
      _=C*(2*B)^2*(scale J 1*scale J 1) :=by ring
      _ ≤ scale J 1*(scale J 1*scale J 1) :=Nat.mul_le_mul_right _ c₂
      _=scale J 3 :=by rw [scale_mul,scale_mul]

end Hierarchy.DescentDatedSeedStartup

end OAI
