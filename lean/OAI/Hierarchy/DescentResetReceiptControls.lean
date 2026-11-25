import OAI.Hierarchy.DescentResetAtlasControlScale
import OAI.Hierarchy.DescentResetReceivedSourcePrice

namespace OAI
/-! Fixed, noncircular local exponents for all original operands of the scheduled
candidate receipt. The source-height parameter is the dimension of the paid Walsh stencil. -/
namespace Hierarchy.DescentDatedAddressBook.ResetMiddle
open DescentSixParty DescentCompiler TerminalScale DescentNamedFundedChart DescentDenseHostOrder Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
variable (t f g reset D : ℕ)
local notation "Ht" => GroupStage.depthBound D n f g

private def shapeConstant (n d depth : ℕ) := 2*((2^n+1)+((2*d+4)*2^n+(2^n+1)*2^(depth+1)))
private def sourceConstant (n d depth host : ℕ) :=
  128+DescentResetTrunkScalar.tableWork+22+16*shapeConstant n d depth+500+23+64+2^host+1

def receiptLocalRate (_board : NonlinearExpanders.Graph n d) (t f g reset D : ℕ) : ℕ :=
  13*localRate G t f g reset D n+(8+((capPeriod G.b t g).map (·+1)).prod)+
    sourceConstant n d (GroupStage.depthBound D n f g) (hostRate t reset)

theorem receipt_controls_at (τ B : ℕ) (den : 0 < B) :
    ∀ᶠ h : ℕ in atTop,∀ copies age p e prev : ℕ,p ≤ h →
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset copies (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let cal:=capCalendar G.b S.rounds g S.height
      let cap:=(cal.take age).prod*256
      let m:=fromCalendar S k (tail τ J) age p f D h e prev n Ht cal
      let b:=S.localWalshBits p (S.groupWidth k (tail τ J) age+k) f (quota S.rounds)
      let limit:=CandidateFront.sourceLimit (roster board k Ht).card (500+23*m.stencil.m+64)
      let budget:=scale J (receiptLocalRate G board t f g reset D)
      2^k ≤ budget ∧ cap ≤ budget ∧ limit ≤ budget ∧ 2^S.hostGain*S.radix ≤ budget ∧ b ≤ budget := by
  filter_upwards [atlas_controls_at G t f g reset τ B D n den] with h control
  intro copies age p e prev bounded J S k cal cap m b limit budget
  let a:=13*localRate G t f g reset D n
  let c:=8+((capPeriod G.b t g).map (·+1)).prod
  let z:=sourceConstant n d Ht (hostRate t reset)
  let P:=scale J a
  have geom:=control copies age p e prev bounded
  have localCap:cap ≤ scale J c:=capPrefix G.b t g J age
  have dim:m.stencil.m ≤ P:=by
    apply le_trans _ ((m.rootControl_le cap (m.stencil.n) (by simp)).trans geom.1)
    change S.groupWidth k (tail τ J) age+k ≤ k+b+2
    dsimp only [b]
    unfold AtomSchedule.localWalshBits DescentWalshPrecision.bits
    omega
  have kroom:2^k ≤ P:=geom.2.1
  have shapes:(roster board k Ht).card ≤ shapeConstant n d Ht*(2*P):=by
    have sh:=roster_bound board k Ht
    rw [pow_succ 2 k] at sh
    apply sh.trans (Nat.mul_le_mul_left _ (by omega))
  have live:1 ≤ P:=Nat.two_pow_pos _
  have source : limit ≤ z*P:=by
    dsimp only [limit,CandidateFront.sourceLimit,z,sourceConstant]
    have constant:=Nat.le_mul_of_pos_right (128+DescentResetTrunkScalar.tableWork+22+500+64) live
    nlinarith only [constant,shapes,dim,Nat.zero_le ((2^hostRate t reset)*P)]
  have member : 2^S.hostGain*S.radix ≤ z*P:=by
    change 2^(hostRate t reset)*2^k ≤ z*P
    exact Nat.mul_le_mul (by dsimp [z,sourceConstant];omega) kroom
  have zfit:z ≤ scale J z:=Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide)
    (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))
  have top:z*P ≤ budget:=by
    change z*scale J a ≤ scale J (a+c+z)
    have mul:=Nat.mul_le_mul_right (scale J a) zfit
    rw [scale_mul] at mul
    exact mul.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
  have small:P ≤ budget:=by
    change scale J a ≤ scale J (a+c+z)
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))
  have capFit:scale J c ≤ budget:=by
    change scale J c ≤ scale J (a+c+z)
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))
  exact ⟨kroom.trans small,localCap.trans capFit,source.trans top,member.trans top,geom.2.2.trans small⟩

end
end Hierarchy.DescentDatedAddressBook.ResetMiddle

end OAI
