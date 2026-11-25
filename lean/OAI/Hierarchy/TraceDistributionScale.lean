import OAI.Computability.VPVNP.CompressionBudget

namespace OAI
/-! # Work and communication estimates at the paired-input trace scale -/

namespace Hierarchy.TraceDistribution

open Filter
open scoped BigOperators Topology

/-- The logarithm of the cap is asymptotic to the volume exponent, and the
number of compression blocks is little-oh of that exponent. -/
structure Scale (u s : ℕ → ℕ) : Prop where
  cap : Tendsto (fun w : ℕ => (u w : ℝ) / w) atTop (𝓝 1)
  blocks : Tendsto (fun w : ℕ => (s w : ℝ) / w) atTop (𝓝 0)

theorem polynomial_room (A b : ℕ) :
    ∀ᶠ w : ℕ in atTop, A * (w+1)^b ≤ 2^(w/100) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (Computability.VPVNP.BurstRAM.eventually_polylog_le (A*100^b) b)
  filter_upwards [eventually_ge_atTop (100*N)] with w hw
  have index : N ≤ w/100 := by omega
  have large : N ≤ 2^(w/100) := index.trans (Nat.lt_two_pow_self.le)
  have bound := hN _ large
  rw [Nat.log2_two_pow] at bound
  calc
    A * (w+1)^b ≤ A * (100*(w/100+1))^b := by gcongr; omega
    _ = (A*100^b) * (w/100+1)^b := by rw [mul_pow,Nat.mul_assoc]
    _ ≤ _ := bound

/-- A uniform bound for both initial bucket sizes and counts. Multiplying either
by a fixed power of the word length and a fixed exponential in the number of
blocks still leaves room below the three-fifths power of the volume. -/
theorem factor_room {u s : ℕ → ℕ} (scale : Scale u s) (A b C : ℕ) :
    ∀ᶠ w : ℕ in atTop, A * (w+1)^b * C^(s w) * 2^(max (w/2) (u w-w/2)) ≤ 2^(3*w/5) := by
  have hcap := (tendsto_order.mp scale.cap).2 (101/100) (by norm_num)
  have hblocks := (tendsto_order.mp scale.blocks).2 (1/(100*((C:ℝ)+1))) (by positivity)
  filter_upwards [hcap,hblocks,polynomial_room A b,eventually_ge_atTop 100] with w hc hs hp hw
  have pos : 0 < (w:ℝ) := by exact_mod_cast (show 0<w by omega)
  have hc' := (div_lt_iff₀ pos).mp hc
  have hs' := (div_lt_iff₀ pos).mp hs
  have blocks' : (s w:ℝ)*(100*((C:ℝ)+1)) < w := by
    apply (lt_div_iff₀ (by positivity : (0:ℝ)<100*((C:ℝ)+1))).mp
    simpa only [one_div,div_eq_inv_mul,mul_one] using hs'
  have hn : 100 * u w ≤ 101 * w := by
    exact_mod_cast (show (100:ℝ)*↑(u w) ≤ 101*w by linarith)
  have hb : 100*(C*s w) ≤ w := by
    exact_mod_cast (show (100:ℝ)*(C*(s w:ℝ)) ≤ w by nlinarith [Nat.cast_nonneg (α:=ℝ) (s w)])
  have expBound : w/100+C*s w+max (w/2) (u w-w/2) ≤ 3*w/5 := by omega
  calc
    _ ≤ 2^(w/100) * (2^C)^(s w) * 2^(max (w/2) (u w-w/2)) := by
      gcongr
      exact Nat.lt_two_pow_self.le
    _ = 2^(w/100+C*s w+max (w/2) (u w-w/2)) := by rw [←pow_mul, ←pow_add, ←pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) expBound

theorem factor_room_real {u s : ℕ → ℕ} (scale : Scale u s) (A b C : ℕ) :
    ∀ᶠ w : ℕ in atTop,
      (A*(w+1)^b*C^(s w)*2^(max (w/2) (u w-w/2)) : ℕ) ≤ ((2:ℝ)^w)^(3/5:ℝ) := by
  filter_upwards [factor_room scale A b C] with w hw
  calc
    ((A*(w+1)^b*C^(s w)*2^(max (w/2) (u w-w/2)) : ℕ) : ℝ) ≤ (2:ℝ)^(3*w/5) := by exact_mod_cast hw
    _ = (2:ℝ)^((3*w/5 : ℕ) : ℝ) := (Real.rpow_natCast ..).symm
    _ ≤ (2:ℝ)^((w:ℝ)*(3/5)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have h : ((3*w/5:ℕ):ℝ)*5 ≤ (3:ℝ)*w := by exact_mod_cast Nat.div_mul_le_self (3*w) 5
      linarith
    _ = _ := by rw [Real.rpow_mul (by norm_num),Real.rpow_natCast]

/-- Any fixed number of lane coordinates per block fits in the high row bits. -/
theorem lane_room {u s : ℕ → ℕ} (scale : Scale u s) (charge : ℕ) :
    ∀ᶠ w : ℕ in atTop, charge*s w ≤ u w+1-w/2 := by
  have lo := (tendsto_order.mp scale.cap).1 (3/4) (by norm_num)
  have hi := (tendsto_order.mp scale.blocks).2 (1/(8*((charge:ℝ)+1))) (by positivity)
  filter_upwards [lo,hi,eventually_ge_atTop 1] with w hl hh hw
  have pos : 0 < (w:ℝ) := by exact_mod_cast (show 0<w by omega)
  have lower := (lt_div_iff₀ pos).mp hl
  have upper := (div_lt_iff₀ pos).mp hh
  have ha : (s w:ℝ)*(8*((charge:ℝ)+1)) < w := by
    apply (lt_div_iff₀ (by positivity : (0:ℝ)<8*((charge:ℝ)+1))).mp
    simpa only [one_div,div_eq_inv_mul,mul_one] using upper
  have low' : 3*w≤4*u w := by exact_mod_cast (show (3:ℝ)*w ≤ 4*u w by linarith)
  have high' : 8*(charge*s w) ≤ w := by
    exact_mod_cast (show (8:ℝ)*(charge*(s w:ℝ)) ≤ w by nlinarith [Nat.cast_nonneg (α:=ℝ) (s w)])
  omega

/-- The saved bits are the actual sum of the terminal arc widths. The additive
term is proportional to the original positions, uniformly in the chosen history. -/
theorem shared_width {E : Type*} [Fintype E] (width : E → ℕ) (mass : E → ℝ)
    (hm : ∀ e, 0 < mass e) (norm : ∑ e, mass e = 1) (energy : ℕ → ℝ)
    {s P W d : ℕ} {err shrink : ℝ} (he : 0 ≤ err) (hs : 2 < shrink)
    (start : 0 ≤ energy 0) (size : Real.sqrt (energy 0) ≤ (d:ℝ)*P*W)
    (step : ∀ i<s, energy (i+1) ≤ energy i/4 + err*((P:ℝ)/shrink^i)^2)
    (stop : (∑ e, (width e:ℝ)^2/mass e) ≤ energy s) :
    (∑ e,(width e:ℝ)) ≤
      ((d:ℝ)*P*W + P*Real.sqrt (4*err/(1-4/shrink^2))) / 2^s := by
  refine (Computability.VPVNP.Compression.widthSum_le_sqrtEnergy (fun e => (width e:ℝ)) mass hm norm).trans
    ((Real.sqrt_le_sqrt stop).trans ?_)
  exact (Computability.VPVNP.Compression.sqrtEnergy_le energy s (P:=P) (by positivity) he hs start step).trans
    (by gcongr)

end Hierarchy.TraceDistribution

end OAI
