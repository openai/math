import OAI.Hierarchy.DescentGlobalControlRoom
import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! Bit cost of clipped word scans with a polynomial shared-table allowance. -/
namespace Hierarchy.DescentCompiler
open DescentCompiler DescentCompiler.TerminalScale Filter
noncomputable section

/-- The first summand pays one original host. The second pays one original group
at its real clipped output pitch. Shared lookups are charged once for all hosts. -/
theorem clipped_date_price (lead price degree rate receiver ratio saving : ℕ) :
    ∃C exponent : ℕ,∀ᶠ h : ℕ in atTop,∀ J hst groups stages copies factor N b width rows w fee : ℕ,
      J ≤ Nat.log 2 h → 2^h ≤ copies → factor ≤ lead*scale J price → N ≤ scale J rate →
      b ≤ scale J rate → width ≤ scale J receiver → w ≤ ratio*h →
      rows*h ≤ (2+N)*h+groups*(32*N*b+16*width) →
      fee ≤ factor*(hst+hst*rows+(h+1)^degree*2^(h/2)) →
      1 ≤ stages →
      fee*w ≤ hst*h*(C*scale J exponent)+hst*(groups*stages)*(C*scale J exponent)+copies/(2^J)^saving := by
  let r:=2*rate+receiver
  refine ⟨64*(lead+1)*(ratio+1),price+r,?_⟩
  filter_upwards [global_control_shared ((lead+1)*(ratio+1)) (degree+1) price 1 saving] with h shared
  intro J H G δ copies factor N b width rows w fee Jle ambient uFit NFit bFit widthFit wFit rowsFit cost radix
  let U:=scale J rate
  let V:=scale J receiver
  let P:=scale J price
  let A:=(lead+1)*(ratio+1)
  let T:=scale J r
  let cap:=64*A*(P*T)
  have pos:1 ≤ U:=Nat.two_pow_pos _
  have bigU:U ≤ T:=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _
    (show rate ≤ r by dsimp [r];omega))
  have bigV:V ≤ T:=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _
    (show receiver ≤ r by dsimp [r];omega))
  have two:U*U ≤ T:=by
    change scale J rate*scale J rate ≤ scale J r
    rw [scale_mul]
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (show rate+rate ≤ r by dsimp [r];omega))
  have first:3+N ≤ 64*T:=by change N ≤ U at NFit; omega
  have second:32*N*b+16*width ≤ 64*T:=by
    have pairs: N*b ≤ T:=(Nat.mul_le_mul NFit bFit).trans two
    change width ≤ V at widthFit
    nlinarith only [pairs,widthFit.trans bigV]
  have funded:factor*w ≤ (A*P)*h:=by
    have mul:=Nat.mul_le_mul (uFit) wFit
    have co:lead*ratio ≤ A:=Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
    calc
      _ ≤ (lead*P)*(ratio*h) := mul
      _ = (lead*ratio)*(P*h) := by ring
      _ ≤ A*(P*h) := Nat.mul_le_mul_right _ co
      _ = _ := by ring
  have priced:=Nat.mul_le_mul_right w cost
  have total:=Nat.mul_le_mul_left (H+H*rows+(h+1)^degree*2^(h/2)) funded
  have scans := Nat.mul_le_mul_left H rowsFit
  have row : (H+H*rows)*h ≤ H*h*(3+N)+(H*G)*(32*N*b+16*width) := by nlinarith only [scans]
  have left:=Nat.mul_le_mul_left (H*h) first
  have right:=Nat.mul_le_mul_left (H*G) second
  have original:(H+H*rows)*h*(A*P) ≤ H*h*cap+(H*G)*cap:=by
    apply (Nat.mul_le_mul_right _ (row.trans (Nat.add_le_add left right))).trans
    dsimp only [cap]
    ring_nf; rfl
  have room:=shared J (price*(J+1)) copies Jle (by simp) ambient
  have small:(h+1)^degree*2^(h/2)*((A*P)*h) ≤ copies/(2^J)^saving:=by
    apply _root_.le_trans _ room
    have sq:=Nat.mul_le_mul_left ((h+1)^degree) (Nat.le_succ h)
    calc
      _ = (A*P*2^(h/2))*((h+1)^degree*h) := by ring
      _ ≤ (A*P*2^(h/2))*((h+1)^degree*(h+1)) := Nat.mul_le_mul_left _ sq
      _ = _ := by dsimp [A,P,scale];rw [pow_succ (h+1) degree];ring
  have block : H*G ≤ H*(G*δ):=Nat.mul_le_mul_left H (Nat.le_mul_of_pos_right G radix)
  have last:=Nat.mul_le_mul_right cap block
  have together:fee*w ≤ H*h*cap+(H*(G*δ))*cap+copies/(2^J)^saving := by
    calc
      _ ≤ (factor*(H+H*rows+(h+1)^degree*2^(h/2)))*w := priced
      _ = (H+H*rows+(h+1)^degree*2^(h/2))*(factor*w) := by ring
      _ ≤ (H+H*rows+(h+1)^degree*2^(h/2))*((A*P)*h) := total
      _ = (H+H*rows)*h*(A*P)+(h+1)^degree*2^(h/2)*((A*P)*h) := by ring
      _ ≤ _ := by omega
  simpa only [cap,A,P,T,Nat.mul_assoc,←scale_mul] using together

end
end Hierarchy.DescentCompiler

end OAI
