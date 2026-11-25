import OAI.Hierarchy.DescentResetWalshScale
import OAI.Hierarchy.DescentSeedEpochRoom

namespace OAI
/-! # Walsh precision at every actual age of the fixed calendar -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler DescentCompiler.TerminalScale DescentDatedSeedStartup Filter
variable {F : Type} [Field F] (G : PoweredGadget F)

theorem walsh_rate (t f g reset τ B:ℕ)(positive:0<B):
    ∀ᶠ h:ℕ in atTop,let J:=Nat.log 2 h/(2*B)
      ∀copies p i:ℕ,let S:=stageNumbers G t J f g reset copies (tail τ J)
        let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
        p≤h→i≤S.length→
        let b:=S.localWalshBits p (S.groupWidth k (tail τ J) i+k) f (quota t)
        8*b≤h ∧ b≤ scale J 3:=by
  let C:=localCoefficient G t f g reset (quota t) τ
  filter_upwards [eventually_late (C*(2*B)^2) B positive,
    eventually_actual_width G t f g reset B (quota t) τ] with h high packed
  let J:=Nat.log 2 h/(2*B)
  dsimp only
  intro copies p i le before
  have small:J≤Nat.log 2 h:=Nat.div_le_self ..
  have tailFit:tail τ J≤τ*(Nat.log 2 h+1)^2:=by
    apply Nat.mul_le_mul_left
    have sq:=Nat.le_self_pow (by decide : 2≠0) (Nat.log 2 h+1)
    omega
  have fit:=packed copies (tail τ J) i p le tailFit before
  have bound:=actual_width G t J f g reset copies (tail τ J) i h p (quota t) τ le small tailFit before
  refine ⟨fit.1.trans (Nat.div_le_self ..),bound.trans ?_⟩
  have one:J≤ scale J 1:=(Nat.le_succ _).trans (by simpa only [scale,one_mul] using (Nat.lt_two_pow_self (n:=J+1)).le)
  have Cfit:C*(2*B)^2≤ scale J 1:=high.trans one
  have logh:=log_epoch h B positive
  calc
    C*(Nat.log 2 h+1)^2 ≤ C*((2*B)*scale J 1)^2:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_left logh _)
    _=C*(2*B)^2*(scale J 1*scale J 1):=by ring
    _≤ scale J 1*(scale J 1*scale J 1):=Nat.mul_le_mul_right _ Cfit
    _=scale J 3:=by rw [scale_mul,scale_mul]

end Hierarchy.DescentSixParty.NativePitch

end OAI
