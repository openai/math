import OAI.Computability.MultitapeWeakETH.RetainedSupply

/-! # Fixed fold ratio and the positive entropy margin -/

namespace OAI.Computability.MultitapeWeakETH.FoldedNetwork

noncomputable section

theorem maskEntropy_nonneg : 0 ≤ entropyBits (1/100) :=
  div_nonneg (Real.binEntropy_nonneg (by norm_num) (by norm_num)) (Real.log_nonneg (by norm_num))

/-- A fold into floor(m/r) terminals has bounded fan-in, and pays at most
one extra block of padding even when n is not divisible by b. -/
theorem fold_size (n b r : ℕ) (hb : 0 < b) (hr : 0 < r) (large : r+2 ≤ n ⌈/⌉ b) :
    let m := n ⌈/⌉ b
    let N := m/r
    0 < N ∧ N ≤ m ∧ m ≤ 2*r*N ∧ m ≤ n ∧ m*b ≤ n+b ∧ r*b ≤ n ∧ r*(N*b) ≤ 2*n := by
  intro m N
  have pos : 0 < N := Nat.div_pos (by omega) hr
  have fan : m ≤ 2*r*N := by
    have rem := Nat.mod_lt m hr
    have split := Nat.mod_add_div m r
    have lower := Nat.le_mul_of_pos_right r pos
    change r ≤ r*(m/r) at lower
    dsimp only [N]
    rw [show 2*r*(m/r) = 2*(r*(m/r)) by ring]
    omega
  have round : m*b ≤ n+b := (Nat.div_mul_le_self (n+b-1) b).trans (by omega)
  have rb : r*b ≤ n := by
    have h := (Nat.mul_le_mul_right b (show r+1 ≤ m by omega)).trans round
    rw [Nat.add_mul,one_mul] at h
    omega
  have m_le_n := (ceilDiv_le_iff_le_mul hb).mpr (Nat.le_mul_of_pos_left n hb)
  refine ⟨pos,Nat.div_le_self ..,fan,m_le_n,round,rb,?_⟩
  calc
    r*(N*b) = (N*r)*b := by ring
    _ ≤ m*b := Nat.mul_le_mul_right b (Nat.div_mul_le_self m r)
    _ ≤ n+b := round
    _ ≤ _ := by have := Nat.le_mul_of_pos_left b hr; omega

/-- A single fold ratio works for every large block count. The gain is
linear in n after accounting for valuation, rounding and mask entropy. -/
theorem fold_margin :
    ∃ (τ : ℝ) (r m₀ : ℕ), 0 < τ ∧ 0 < r ∧ r+2 ≤ m₀ ∧ ∀ n b, 0 < b → m₀ ≤ n ⌈/⌉ b →
      let m := n ⌈/⌉ b
      let N := m/r
      0 < retainedInfo n (N*b) ∧
      τ*n ≤ retainedInfo n (N*b)-maskCost n b/Real.sqrt 2 ∧
      maskCost n b ≤ 8*entropyBits (1/100)*n := by
  let H := entropyBits (1/100)
  let R := Real.sqrt 2
  have rp : 0 < R := by positivity
  have Hpos : 0 ≤ H := maskEntropy_nonneg
  let gap := gamma-4*rho-4*H/R
  have gp : 0 < gap := by
    have h := trace_density_margin
    dsimp [gap,gamma,rho,H,R]
    ring_nf at h ⊢
    linarith
  obtain ⟨r,hr⟩ := exists_nat_gt (max 1 ((4*gamma+4*H/R)/(gap/4)))
  have rpos : 0 < r := by have := (le_max_left ..).trans_lt hr; exact_mod_cast (by linarith : (0:ℝ)<r)
  have ratio := (div_lt_iff₀ (by positivity : 0 < gap/4)).mp ((le_max_right ..).trans_lt hr)
  obtain ⟨m₁,hm₁⟩ := exists_nat_ge (Real.logb 2 (quadConstant gamma)/(gap/4))
  refine ⟨gap/2,r,max (r+2) m₁,by positivity,rpos,le_max_left ..,?_⟩
  intro n b hb large m N
  obtain ⟨_,_,_,mn,round,rb,period⟩ := fold_size n b r hb rpos ((le_max_left ..).trans large)
  have nh : 0 < n := by omega
  have bn : b ≤ n := (Nat.le_mul_of_pos_left b rpos).trans rb
  have mask : maskCost n b ≤ 4*H*(n+b) := by
    unfold maskCost
    push_cast
    calc
      _ = 4*H*((m*b:ℕ):ℝ) := by push_cast; ring
      _ ≤ _ := by gcongr; exact_mod_cast round
  have sum : maskCost n b ≤ 8*H*n := by
    have bound : (b:ℝ) ≤ n := by exact_mod_cast bn
    nlinarith only [mask,mul_le_mul_of_nonneg_left bound Hpos]
  have bdiv : (b:ℝ) ≤ n/r := (le_div_iff₀ (Nat.cast_pos.mpr rpos)).mpr (by
    rw [mul_comm]; exact_mod_cast rb)
  have Bdiv : ((N*b:ℕ):ℝ) ≤ 2*n/r := (le_div_iff₀ (Nat.cast_pos.mpr rpos)).mpr (by
    rw [mul_comm]; exact_mod_cast period)
  have losses : (4*gamma+4*H/R)*((n:ℝ)/r) ≤ gap/4*n := by
    have h := mul_le_mul_of_nonneg_right ratio.le (show 0 ≤ (n:ℝ)/r by positivity)
    convert h using 1
    field_simp
  have constant : Real.logb 2 (quadConstant gamma) ≤ gap/4*n := by
    have h := (div_le_iff₀ (by positivity : 0 < gap/4)).mp hm₁
    have hn : (m₁:ℝ) ≤ n := by exact_mod_cast ((le_max_right ..).trans large).trans mn
    nlinarith only [h,mul_le_mul_of_nonneg_left hn (show 0 ≤ gap/4 by positivity)]
  have adv := div_le_div_of_nonneg_right mask rp.le
  have penalty := mul_le_mul_of_nonneg_left Bdiv (show 0 ≤ 2*gamma by have := gamma_range.1; positivity)
  have pad := mul_le_mul_of_nonneg_left bdiv (show 0 ≤ 4*H/R by positivity)
  have gain : gap/2*n ≤ retainedInfo n (N*b)-maskCost n b/R := by
    unfold retainedInfo
    dsimp only [gap] at losses constant ⊢
    ring_nf at adv pad losses penalty constant ⊢
    linarith only [adv,pad,losses,penalty,constant]
  have pos : 0 < gap/2*(n:ℝ) := by positivity
  have charge : 0 ≤ maskCost n b/R := by unfold maskCost; have := maskEntropy_nonneg; positivity
  exact ⟨by linarith only [pos,gain,charge],gain,sum⟩

end
end OAI.Computability.MultitapeWeakETH.FoldedNetwork
