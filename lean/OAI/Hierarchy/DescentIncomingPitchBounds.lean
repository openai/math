import OAI.Hierarchy.DescentTerminalRawSpanBound

namespace OAI
/-! # Packing a public group coordinate at the actual Walsh and final terminal widths -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentResetGates DescentPrimitivePalette DescentCompiler DescentCompiler.TerminalScale Filter
noncomputable section

/-- Removing the block coordinate from the Walsh lane leaves either all groups in one
word or a group pitch dense at the original local precision times the block count. -/
theorem reset_density (n k h b : ℕ) (hb:0<b) (room:8*b≤h) :
    let l:=min (n+k) (Nat.log 2 (h/(8*b)))
    let M:=2^(l-k)
    0<M ∧ M≤h/2 ∧ (2^n≤M ∨ h≤M*(16*2^k*b)):=by
  intro l M
  have divpos:0<h/(8*b):=Nat.div_pos room (by omega)
  have bound:2^l≤h/(8*b):=(Nat.pow_le_pow_right (by decide) (min_le_right ..)).trans (Nat.pow_log_le_self 2 divpos.ne')
  have scaleM:M≤2^l:=Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
  have limit:2^l*(8*b)≤h:=(Nat.le_div_iff_mul_le (by omega)).mp bound
  refine ⟨Nat.two_pow_pos _,(Nat.le_div_iff_mul_le (by decide)).2 ?_,?_⟩
  · exact (Nat.mul_le_mul scaleM (show 2≤8*b by omega)).trans limit
  · by_cases covered:l=n+k
    · left; simp [M,covered]
    · right
      have exp:l=Nat.log 2 (h/(8*b)):=by dsimp only [l] at *;omega
      have upper:=Nat.lt_pow_succ_log_self (by decide : 1<2) (h/(8*b))
      rw [←exp,pow_succ] at upper
      have width:h<(2^l*2)*(8*b):=(Nat.div_lt_iff_lt_mul (by omega)).mp upper
      have cube:2^l≤M*2^k:=by dsimp only [M];rw [←pow_add];apply Nat.pow_le_pow_right (by decide);omega
      calc
        h ≤ (2^l*2)*(8*b):=width.le
        _ ≤ ((M*2^k)*2)*(8*b):=Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ cube)
        _=M*(16*2^k*b):=by ring

/-- The hardware-width calibration for the actual raw terminal node page also pays
the exposed terminal group count, including any completely empty ordinary history. -/
theorem terminal_half {F:Type} [Field F] (G:PoweredGadget F) (op:RotorSpec) (drift t f g reset τ B:ℕ)
    (branch:G.b≤2^(capRate G t g))(positive:0<B)
    (budget:2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19))≤B):
    ∀ᶠ h:ℕ in atTop,let J:=Nat.log 2 h/(2*B)
      ∀copies p:ℕ,let S:=stageNumbers G t J f g reset copies (TerminalScale.tail τ J)
        p≤h→0<S.groupCount S.length ∧ S.groupCount S.length≤h/2:=by
  filter_upwards [terminal_raw_room G op drift t f g reset τ B branch positive budget] with h available
  intro J copies p S fit
  let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
  have raw : 32*((S.groupCount S.length*2^k)*actualRawSpan G S op p drift)≤h :=
    available copies p 0 fit (Nat.zero_le _)
  have blocks : S.groupCount S.length≤S.groupCount S.length*2^k :=
    Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have span_pos : 0<actualRawSpan G S op p drift := Nat.succ_pos _
  have paid := blocks.trans (Nat.le_mul_of_pos_right _ span_pos)
  refine ⟨?_,(Nat.le_div_iff_mul_le (by decide : 0<2)).2 ?_⟩
  · simp only [AtomSchedule.groupCount,Nat.sub_self,pow_zero,Nat.mul_one]
    exact Nat.two_pow_pos _
  · calc
      S.groupCount S.length*2 = 2*S.groupCount S.length := Nat.mul_comm _ _
      _ ≤ 2*((S.groupCount S.length*2^k)*actualRawSpan G S op p drift) := Nat.mul_le_mul_left 2 paid
      _ ≤ 32*((S.groupCount S.length*2^k)*actualRawSpan G S op p drift) := Nat.mul_le_mul_right _ (by decide : 2≤32)
      _ ≤ h := raw

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
