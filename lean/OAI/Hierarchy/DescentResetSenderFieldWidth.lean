import OAI.Hierarchy.DescentSenderBoardHeight
import OAI.Hierarchy.DescentResetMiddleCalendar
import OAI.Hierarchy.DescentResetRosterFunctions
import OAI.Hierarchy.DescentDenseHostOrder
import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # The actual sender lookup fields fit their common packed word -/
namespace Hierarchy.DescentDatedAddressBook.ResetMiddle
open DescentResetLocalRoster DescentDenseHostOrder DescentCompiler DescentCompiler.TerminalScale Filter
open scoped Classical
noncomputable section
variable (D cap n k Ht : ℕ)

theorem sender_field : senderWidth k n Ht cap ≤ fieldWidth D cap n k Ht :=
  (le_max_right ..).trans ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..)))

private theorem box :
    (2^k * 2^k * 2^n * 2^n * 2^Ht * 2^(Nat.clog 2 (cap+1))) * 1024 ≤ 2^(fieldWidth D cap n k Ht) := by
  apply le_trans _ (Nat.pow_le_pow_right (by decide) (sender_field D cap n k Ht))
  unfold senderWidth
  rw [show 2*k=k+k by omega,show 2*n=n+n by omega]
  simp only [pow_add]
  norm_num
  ring_nf
  exact le_rfl

theorem sender_keys : rootSlots k (2^n)*(2^n+2^Ht)<2^fieldWidth D cap n k Ht :=by
  let K:=2^k
  let Y:=2^n
  let T:=2^Ht
  let A:=2^(Nat.clog 2 (cap+1))
  have hk : 0<K:=Nat.two_pow_pos _
  have hy : 0<Y:=Nat.two_pow_pos _
  have ht : 0<T:=Nat.two_pow_pos _
  have ha : 0<A:=Nat.two_pow_pos _
  have ky : K≤K*Y:=Nat.le_mul_of_pos_right _ hy
  have extra : Y+T≤2*(Y*T):=by
    have h₁:=Nat.le_mul_of_pos_right Y ht
    have h₂:=Nat.le_mul_of_pos_left T hy
    omega
  have num : rootSlots k Y≤6*(K*Y):=by
    unfold rootSlots
    rw [pow_succ]
    change K*2+K*2*(Y+1)≤_
    nlinarith only [ky]
  have paid : 12*(K*Y*Y*T)<1024*(K*K*Y*Y*T*A):=by
    let v:=K*Y*Y*T
    have hv : 0<v:=by dsimp [v];positivity
    have upper : v≤K*K*Y*Y*T*A:=by
      calc v≤K*v := Nat.le_mul_of_pos_left _ hk
           _ ≤ (K*v)*A := Nat.le_mul_of_pos_right _ ha
           _ = _ :=by dsimp [v];ring
    change 12*v<1024*(K*K*Y*Y*T*A)
    omega
  have result:=Nat.mul_le_mul num extra
  exact result.trans_lt ((show 6*(K*Y)*(2*(Y*T))< (K*K*Y*Y*T*A)*1024 by nlinarith only [paid]).trans_le
    (box D cap n k Ht))

theorem sender_old_slots : 2^k*(2*cap)<2^fieldWidth D cap n k Ht :=by
  let K:=2^k
  let Y:=2^n
  let T:=2^Ht
  let A:=2^(Nat.clog 2 (cap+1))
  have capFit : cap<A:=Nat.le_pow_clog (by decide) (cap+1)
  have hk : 0<K:=Nat.two_pow_pos _
  have hy : 0<Y:=Nat.two_pow_pos _
  have ht : 0<T:=Nat.two_pow_pos _
  have withK : K≤K*K:=Nat.le_mul_of_pos_left _ hk
  have full : K*A≤K*K*Y*Y*T*A:=by
    apply Nat.mul_le_mul_right A
    exact ((withK.trans (Nat.le_mul_of_pos_right _ hy)).trans (Nat.le_mul_of_pos_right _ hy)).trans
      (Nat.le_mul_of_pos_right _ ht)
  have below:=Nat.mul_lt_mul_of_pos_left capFit hk
  apply lt_of_lt_of_le _ (box D cap n k Ht)
  change K*(2*cap)<(K*K*Y*Y*T*A)*1024
  nlinarith only [full,below]

theorem sender_shapes {d : ℕ} (board : NonlinearExpanders.Graph n d) (wide : d≤2^k) :
    (roster board k Ht).card≤2^fieldWidth D cap n k Ht :=by
  let K:=2^k
  let Y:=2^n
  let T:=2^Ht
  let A:=2^(Nat.clog 2 (cap+1))
  have hk : 0<K:=Nat.two_pow_pos _
  have hy : 0<Y:=Nat.two_pow_pos _
  have ht : 0<T:=Nat.two_pow_pos _
  have ha : 0<A:=Nat.two_pow_pos _
  let v:=K*Y*T
  have yt : Y*T≤v:=by simpa [v,Nat.mul_assoc] using Nat.le_mul_of_pos_left (Y*T) hk
  have ky : K*Y≤v:=Nat.le_mul_of_pos_right _ ht
  have y : Y≤v:=(Nat.le_mul_of_pos_right _ ht).trans yt
  have t : T≤v:=(Nat.le_mul_of_pos_left _ hy).trans yt
  have dy : d*Y≤v:=(Nat.mul_le_mul_right Y wide).trans ky
  have sum : (Y+1)+((2*d+4)*Y+(Y+1)*(T*2))≤12*v:=by nlinarith only [y,yt,t,dy,hy]
  have last : K*v≤K*K*Y*Y*T*A:=by
    calc K*v≤(K*v)*Y:=Nat.le_mul_of_pos_right _ hy
         _ ≤ ((K*v)*Y)*A:=Nat.le_mul_of_pos_right _ ha
         _ = _ :=by dsimp[v];ring
  have limit:=Nat.mul_le_mul (Nat.mul_le_mul_left 2 sum) (le_refl (K*2))
  apply (roster_bound board k Ht).trans
  rw [show 2^(Ht+1)=T*2 by rw [pow_succ],show 2^(k+1)=K*2 by rw [pow_succ]]
  apply limit.trans
  apply le_trans _ (box D cap n k Ht)
  change 2*(12*v)*(K*2)≤(K*K*Y*Y*T*A)*1024
  nlinarith only [last]

end
end Hierarchy.DescentDatedAddressBook.ResetMiddle

end OAI
