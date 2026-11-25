import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! The bit and ROM bounds for the six measured terminal role fields on the chosen common scale. -/
namespace Hierarchy.DescentTerminalSliceShelf
open DescentCompiler.TerminalScale Filter
noncomputable section

theorem digits_of_room (h groups A d j σ α:ℕ) (g:0<groups)
    (paid:32*(groups*scale j (σ+α))≤h)
    (width:d≤groups*scale j σ) (slots:A≤scale j α) :
    d*(2+3*A)+Nat.clog 2 ((2+3*A)+1)≤h/2 := by
  have u:1≤scale j σ:=Nat.two_pow_pos _
  have z:1≤scale j α:=Nat.two_pow_pos _
  have enough:2+3*A≤5*scale j α:=by omega
  have log_:Nat.clog 2 ((2+3*A)+1)≤2+3*A:=(Nat.clog_le_iff_le_pow (by decide)).mpr
    (show (2+3*A)+1≤2^(2+3*A) from Nat.lt_two_pow_self)
  have price:=Nat.mul_le_mul width enough
  have high:scale j α≤groups*scale j σ*scale j α:=Nat.le_mul_of_pos_left _ (Nat.mul_pos g u)
  rw [←scale_mul] at paid
  apply (Nat.le_div_iff_mul_le (by decide:0<2)).mpr
  nlinarith only [paid,price,enough,high,log_]

theorem attained_digits (τ σ α B:ℕ) (hb:0<B) (bought:2*(τ+(σ+α))≤B) :
    ∀ᶠh:ℕ in atTop,let j:=Nat.log 2 h/(2*B)
      ∀groups A d:ℕ,0<groups→groups≤2^(tail τ j)→
        d≤groups*scale j σ→A≤scale j α→
        d*(2+3*A)+Nat.clog 2 ((2+3*A)+1)≤h/2 := by
  filter_upwards [eventually_home τ 0 (σ+α) B hb (by simpa using bought)] with h paid
  intro j groups A d positive cap width slots
  apply digits_of_room h groups A d j σ α positive _ width slots
  exact paid.2 0 groups _ (by simpa using cap) (by simp) le_rfl

theorem table_words (d L h:ℕ) (positive:0<L) (room:d*L+Nat.clog 2 (L+1)≤h/2) :
    L*2^d+2^(d*L)≤2*2^(h/2) := by
  have mul:=Nat.le_mul_of_pos_right d positive
  have count:L≤2^Nat.clog 2 (L+1):=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have shift:=Nat.mul_le_mul_right (2^d) count
  rw [←pow_add] at shift
  have a : 2^(Nat.clog 2 (L+1)+d)≤2^(h/2):=Nat.pow_le_pow_right (by decide) (by omega)
  have b : 2^(d*L)≤2^(h/2):=Nat.pow_le_pow_right (by decide) (by omega)
  omega

end
end Hierarchy.DescentTerminalSliceShelf

end OAI
