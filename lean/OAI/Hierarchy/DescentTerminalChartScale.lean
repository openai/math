import OAI.Hierarchy.DescentStackScale

namespace OAI
/-! # A single dyadic residual population pays for common hosts and fits the short terminal lookup -/
namespace Hierarchy.DescentCompiler.TerminalScale
open Filter

def tail (τ J : ℕ) := τ*(J+1)
def T (J : ℕ) := 2^J
def scale (J a : ℕ) := 2^(a*(J+1))

theorem residual (τ J : ℕ) : 2^(tail τ J)=(2*T J)^τ := by
  simp only [tail,T,show 2*2^J=2^(J+1) by rw [pow_succ,Nat.mul_comm],←pow_mul,Nat.mul_comm τ]

/-- An arbitrary fixed coefficient and polynomial in log R are absorbed after τ is chosen. -/
theorem logarithmic (c d τ J : ℕ) (late : c*(τ+1)^d≤2^(J+1)) :
    c*(tail τ J+1)^d≤scale J (d+1) := by
  have jBound : J+1≤2^(J+1):= (Nat.lt_two_pow_self (n:=J+1)).le
  have room : tail τ J+1≤(τ+1)*2^(J+1) := by
    unfold tail
    calc
      τ*(J+1)+1≤(τ+1)*(J+1) := by rw [Nat.add_mul,Nat.one_mul];omega
      _ ≤ _ := Nat.mul_le_mul_left _ jBound
  calc
    c*(tail τ J+1)^d ≤ c*((τ+1)*2^(J+1))^d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left room d)
    _ = (c*(τ+1)^d)*(2^(J+1))^d := by rw [mul_pow,Nat.mul_assoc]
    _ ≤ 2^(J+1)*(2^(J+1))^d := Nat.mul_le_mul_right _ late
    _ = scale J (d+1) := by unfold scale;rw [←pow_mul,←pow_add];congr 1;ring

theorem scale_mul (J a b : ℕ) : scale J a*scale J b=scale J (a+b) := by
  unfold scale;rw [←pow_add,Nat.add_mul]

/-- First choose τ using the degree of the shared-host price, including the true payload width h/p. -/
theorem reserve (c d a q τ J cost h p : ℕ)
    (late : c*(τ+1)^d≤2^(J+1)) (enough : a+(d+1)+q≤τ)
    (shared : cost≤scale J a*(c*(tail τ J+1)^d)) (packing : h≤p*scale J q) :
    cost*h≤p*2^(tail τ J) := by
  have pay : cost≤scale J (a+(d+1)) := by
    rw [←scale_mul]
    exact shared.trans (Nat.mul_le_mul_left _ (logarithmic c d τ J late))
  calc
    cost*h ≤ scale J (a+(d+1))*(p*scale J q) := Nat.mul_le_mul pay packing
    _ = p*(scale J (a+(d+1))*scale J q) := by ring
    _ = p*scale J (a+(d+1)+q) := congrArg (p*·) (scale_mul J (a+(d+1)) q)
    _ ≤ _ := Nat.mul_le_mul_left p (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ enough))

theorem home_width (τ κ σ J k V span : ℕ) (allSites : V≤2^(tail τ J)*2^k)
    (common : k≤κ*(J+1)) (localBits : span≤scale J σ) :
    V*span≤scale J (τ+κ+σ) := by
  have sites : V≤scale J (τ+κ) := by
    rw [←scale_mul]
    exact allSites.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) common))
  rw [←scale_mul]
  exact Nat.mul_le_mul sites localBits

/-- The same B gives the h/32 budget to every genuine per-home record, before reading any histories. -/
theorem eventually_home (τ κ σ B : ℕ) (hB : 0<B) (bought : 2*(τ+κ+σ)≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B);
      0<J ∧ ∀k V span : ℕ,V≤2^(tail τ J)*2^k→k≤κ*(J+1)→span≤scale J σ→
        32*(V*span)≤h := by
  filter_upwards [age_room B hB] with h feasible
  let J:=Nat.log 2 h/(2*B)
  change 0<J ∧ 32*(2^J)^B≤h at feasible
  refine ⟨feasible.1,?_⟩
  intro k V span sites common localBits
  have lift : (τ+κ+σ)*(J+1)≤J*B := by
    have a:=Nat.mul_le_mul_left (τ+κ+σ) (show J+1≤2*J by omega)
    have b:=Nat.mul_le_mul_left J bought
    nlinarith only [a,b]
  have cap : scale J (τ+κ+σ)≤(2^J)^B := by
    rw [←pow_mul];exact Nat.pow_le_pow_right (by decide) lift
  exact (Nat.mul_le_mul_left 32 ((home_width τ κ σ J k V span sites common localBits).trans cap)).trans feasible.2

/-- Any prescribed finite threshold on the age is eventually attained after fixing the exponent. -/
theorem eventually_late (K B : ℕ) (pos : 0<B) :
    ∀ᶠ h : ℕ in atTop, K≤Nat.log 2 h/(2*B) := by
  filter_upwards [eventually_ge_atTop (2^(K*(2*B)))] with h large
  have nz : h≠0 := ((Nat.two_pow_pos _).trans_le large).ne'
  apply (Nat.le_div_iff_mul_le (show 0<2*B by omega)).mpr
  exact (Nat.le_log_iff_pow_le (by decide) nz).mpr large

end Hierarchy.DescentCompiler.TerminalScale

end OAI
