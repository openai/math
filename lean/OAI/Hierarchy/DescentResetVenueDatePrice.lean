import OAI.Hierarchy.DescentResetClippedDatePrice

namespace OAI
/-! The shared output venue charges its current and successor row pitches at their own densities. -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler DescentCompiler.TerminalScale Filter
noncomputable section

private theorem scale_monotone (J : ℕ) {a b : ℕ} (h : a≤b) : scale J a≤ scale J b :=
  Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ h)

private theorem double_scale (J a : ℕ) : 2*scale J a≤ scale J (a+1) :=by
  unfold scale
  rw [Nat.mul_comm 2,←Nat.pow_succ]
  exact Nat.pow_le_pow_right (by decide) (by rw [Nat.succ_mul];omega)

theorem venue_date_price (lead exponent localRate receiver nextRate ratio saving : ℕ) :
    ∃C E : ℕ,∀ᶠ h : ℕ in atTop,∀ J H G Gnext stages copies factor N b width rows nextRows w fee : ℕ,
      J≤Nat.log 2 h → 2^h≤copies → factor≤lead*scale J exponent → N≤ scale J localRate →
      b≤ scale J localRate → width≤ scale J receiver → w≤ratio*h →
      rows*h≤(2+N)*h+G*(32*N*b+16*width) →
      H*nextRows*h≤H*h+H*Gnext*scale J nextRate → Gnext≤G → 0<H →
      fee≤factor*(1+H+H*rows+H*nextRows+(h+1)^3*2^(h/2)) → 1≤ stages →
      fee*w≤H*h*(C*scale J E)+H*(G*stages)*(C*scale J E)+copies/(2^J)^saving := by
  obtain ⟨C,E,late⟩:=clipped_date_price (2*lead) exponent 3 (localRate+1) (receiver+nextRate+1) ratio saving
  refine ⟨C,E,?_⟩
  filter_upwards [late] with h bound
  intro J H G Gnext stages copies factor N b width rows nextRows w fee logJ files pay cells digits wide cpu
    old next smaller occupied work stagesPos
  let V:=scale J nextRate
  have room : nextRows*h≤h+Gnext*V :=by
    apply Nat.le_of_mul_le_mul_left (c:=H) _ occupied
    simpa only [Nat.mul_add,Nat.mul_assoc,V] using next
  have U : 1≤ scale J localRate :=Nat.two_pow_pos _
  have n : N+1≤ scale J (localRate+1) :=by
    apply _root_.le_trans _ (double_scale J localRate);omega
  have b' := digits.trans (scale_monotone J (Nat.le_succ localRate))
  have w' : width+V≤ scale J (receiver+nextRate+1) :=by
    apply _root_.le_trans _ (double_scale J (receiver+nextRate))
    have l:=wide.trans (scale_monotone J (Nat.le_add_right receiver nextRate))
    have r : V≤ scale J (receiver+nextRate):=scale_monotone J (Nat.le_add_left ..)
    omega
  have scan : (rows+nextRows)*h≤(2+(N+1))*h+G*(32*(N+1)*b+16*(width+V)) :=by
    have extra:=Nat.mul_le_mul_right V smaller
    have both:=Nat.add_le_add old (room.trans (Nat.add_le_add_left extra _))
    nlinarith only [both]
  have factor' : 2*factor≤2*lead*scale J exponent:=by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 pay
  have invoice : fee≤(2*factor)*(H+H*(rows+nextRows)+(h+1)^3*2^(h/2)) :=by
    apply work.trans
    have double_budget (hosts current successor shared : ℕ) (live : 0<hosts) :
        1+hosts+current+successor+shared ≤ 2*(hosts+(current+successor)+shared) := by
      omega
    have : 1+H+H*rows+H*nextRows+(h+1)^3*2^(h/2)≤2*(H+H*(rows+nextRows)+(h+1)^3*2^(h/2)) :=by
      rw [Nat.mul_add H rows nextRows]
      exact double_budget H (H*rows) (H*nextRows) _ occupied
    simpa only [Nat.mul_left_comm,Nat.mul_assoc] using Nat.mul_le_mul_left factor this
  exact bound J H G stages copies (2*factor) (N+1) b (width+V) (rows+nextRows) w fee
    logJ files factor' n b' w' cpu scan invoice stagesPos

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
