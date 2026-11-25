import OAI.LinearAlgebra.FiniteFourier.PackedWidthCost
import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.AtTwoPrimeGridCircuit
import OAI.LinearAlgebra.FiniteFourier.JetAssembly.JetOpenAssemblyCost

/-! # Gate costs of the two-local packed transforms

Each tensor word is charged on its full working array including the borrowed
registers. At a fixed height the data widths of all the summands add to the
prime product. Taylor shifts, gathering, and the three child encoders share
the same per-coefficient budget.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace AtTwoCost

open Real Finset

/-- Work per entry of the unextended short jet in the packed budget. -/
noncomputable def rate (n r s : ℕ) (B β : ℝ) : ℝ :=
  (1+log B)^2 * ((1+logb 2 n)^β + (1+log (2+r))*convolutionEnvelope s)

private theorem kernel_nonneg {n : ℕ} (hn : 0 < n) (β : ℝ) : 0 ≤ (1+logb 2 n)^β :=
  by
  have h := logb_nonneg (by norm_num : (1:ℝ)<2) (show (1:ℝ) ≤ n by exact_mod_cast hn)
  exact rpow_nonneg (by linarith) _

private theorem jet_log {r : ℕ} : 0 ≤ log (2+(r:ℝ)) := log_nonneg (by have := Nat.cast_nonneg (α := ℝ) r; linarith)

theorem envelope_le_rate {n r s : ℕ} {B β : ℝ} (hn : 0 < n) (hs : 0 < s) (hB : 1 ≤ B) :
    convolutionEnvelope s ≤ rate n r s B β := by
  have hE := convolutionEnvelope_one_le hs
  have hL := log_nonneg hB
  have hJ := jet_log (r := r)
  have hk := kernel_nonneg hn β
  unfold rate
  calc
    _ ≤ (1+log (2+r))*convolutionEnvelope s := by nlinarith only [mul_nonneg hJ (zero_le_one.trans hE)]
    _ ≤ (1+logb 2 n)^β + _ := le_add_of_nonneg_left hk
    _ ≤ _ := le_mul_of_one_le_left (by positivity) (by nlinarith [sq_nonneg (log B)])

private theorem kernel_width {W n : ℕ} {K β : ℝ} (hn : 0 < n) (hW : 0 < W)
    (hK : 1 ≤ K) (hcap : (W : ℝ) ≤ K*n) (hβ : 0 ≤ β) :
    (1+logb 2 W)^β ≤ (1+logb 2 K)^β*(1+logb 2 n)^β := by
  have h₂ : (1:ℝ) < 2 := by norm_num
  have hnL := logb_nonneg h₂ (show 1 ≤ (n:ℝ) by exact_mod_cast hn)
  have hKL := logb_nonneg h₂ hK
  have hWL := logb_nonneg h₂ (show 1 ≤ (W:ℝ) by exact_mod_cast hW)
  rw [← mul_rpow (by linarith) (by linarith)]
  apply rpow_le_rpow (by linarith) _ hβ
  have h := logb_le_logb_of_le h₂ (show 0 < (W:ℝ) by exact_mod_cast hW) hcap
  rw [logb_mul (by linarith) (by positivity)] at h
  nlinarith only [h, mul_nonneg hKL hnL]

/-- Price a synchronized word on one summand of data width `v`. The
factor `K` bounds total registers per data register, and the depth bound
`L (1+log B)^2` accommodates both prime and endpoint changes of basis. -/
theorem word_le {n e r h s v W D : ℕ} {B K L C β : ℝ}
    (hn : 0 < n) (hs : 0 < s) (hβ : 0 ≤ β)
    (hC : 0 ≤ C) (hK : 1 ≤ K) (hL : 0 ≤ L)
    (hv : v ≤ n) (hW : 0 < W) (hcap : (W:ℝ) ≤ K*v) (hh : h ≤ 4*r)
    (hD : (D:ℝ) ≤ L*(1+log B)^2) :
    (D : ℝ)*(W*(40*e*h*convolutionEnvelope s) + (2*e*h)*(C*W*(1+logb 2 W)^β)) ≤
      (4*K*L*(40 + 2*C*(1+logb 2 K)^β)) * (v*e*r) * rate n r s B β := by
  have hK' := zero_le_one.trans hK
  have hE := zero_le_one.trans (convolutionEnvelope_one_le hs)
  have hj := jet_log (r := r)
  have hx := kernel_nonneg hn β
  have hk := kernel_width hn hW hK (hcap.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hv) hK')) hβ
  let A := (1+logb 2 K)^β
  let X := (1+logb 2 n)^β
  let Y := (1+log (2+r))*convolutionEnvelope s
  have hA : 0 ≤ A := rpow_nonneg (by linarith [logb_nonneg (by norm_num : (1:ℝ)<2) hK]) _
  have hEY : convolutionEnvelope s ≤ Y := by
    dsimp [Y]
    nlinarith only [mul_nonneg hj hE]
  have hY : 0 ≤ Y := hE.trans hEY
  have hh' : (h:ℝ) ≤ 4*r := by exact_mod_cast hh
  have hk' : (1+logb 2 W)^β ≤ A*X := hk
  have hcore : 40*convolutionEnvelope s + 2*C*(1+logb 2 W)^β ≤
      (40+2*C*A)*(X+Y) := by
    nlinarith only [hEY, mul_le_mul_of_nonneg_left hk' (by positivity : 0 ≤ 2*C),
      mul_nonneg (show 0 ≤ 2*C*A by positivity) hY, hx]
  calc
    _ = (D*W*e*h : ℝ)*(40*convolutionEnvelope s + 2*C*(1+logb 2 W)^β) := by ring
    _ ≤ ((L*(1+log B)^2)*(K*v)*e*(4*r))*((40+2*C*A)*(X+Y)) := by
      apply mul_le_mul _ hcore (by have := kernel_nonneg hW β; positivity) (by positivity)
      gcongr
    _ = _ := by unfold rate; dsimp [A, X, Y]; ring

/-- Price one Taylor shift on the `v` rows of a summand, in either direction.
The degree and each height may vary below the common long-jet bound. -/
theorem taylor_le {n e r h v s : ℕ} {β B : ℝ} (hn : 0 < n) (hh : 0 < h)
    (hmax : h ≤ 4*r) (hs : 0 < s) (hB : 1 ≤ B) :
    (v:ℝ)*(8*e*h*(1+logb 2 h)*convolutionEnvelope s) ≤
      192*(v*e*r)*rate n r s B β := by
  have hJ := jet_log (r := r)
  have hh' : (h:ℝ) ≤ 4*r := by exact_mod_cast hmax
  have hE := zero_le_one.trans (convolutionEnvelope_one_le hs)
  have hl : log h ≤ log 4 + log (2+(r:ℝ)) := by
    rw [← log_mul (by norm_num) (by positivity)]
    apply log_le_log (by exact_mod_cast hh)
    linarith
  have htwo := log_two_gt_d9
  have hfour : log 4 = 2*log 2 := by rw [show (4:ℝ) = 2^2 by norm_num, log_pow]; norm_num
  have hscale : 1+logb 2 h ≤ 6*(1+log (2+(r:ℝ))) := by
    rw [logb, ← le_sub_iff_add_le', div_le_iff₀ (by linarith)]
    nlinarith only [hfour, hl, htwo, mul_nonneg hJ (show 0 ≤ log 2 - 1/2 by linarith), hJ]
  have hhL : 0 ≤ 1+logb 2 h := by
    have := logb_nonneg (by norm_num : (1:ℝ)<2) (show (1:ℝ) ≤ h by exact_mod_cast hh)
    linarith
  have hlog := log_nonneg hB
  have hbase := kernel_nonneg hn β
  have htail : (1+log (2+(r:ℝ)))*convolutionEnvelope s ≤ rate n r s B β := by
    unfold rate
    calc
      _ ≤ (1+logb 2 n)^β + _ := le_add_of_nonneg_left hbase
      _ ≤ _ := le_mul_of_one_le_left (by positivity) (by nlinarith [sq_nonneg (log B)])
  calc
    _ ≤ (v:ℝ)*(8*e*(4*r)*(6*(1+log (2+(r:ℝ))))*convolutionEnvelope s) := by gcongr
    _ = 192*(v*e*r)*((1+log (2+(r:ℝ)))*convolutionEnvelope s) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htail (by positivity)

/-- Absolute depth factor for the prime change of basis on a product grid.
The same estimate dominates the endpoint words. -/
theorem stage_depth {B : ℕ} (hB : 6 ≤ B) :
    ((243*(84+6400*(1+Nat.clog 2 (2+B))) : ℕ):ℝ) ≤ 8000000*(1+log B)^2 := by
  have hb : 2 ≤ (B:ℝ) := by exact_mod_cast (show 2 ≤ B by omega)
  have hL := log_nonneg (show 1 ≤ (B:ℝ) by linarith)
  have hlog : log (2+B : ℝ) ≤ log 2 + log B := by
    rw [← log_mul (by norm_num) (by linarith)]
    apply log_le_log (by positivity)
    linarith
  have hcl : (Nat.clog 2 (2+B) : ℝ) ≤ 1 + logb 2 (2+B) := by
    rw [← natCeil_logb_natCast]
    push_cast
    exact (Nat.ceil_lt_add_one (logb_nonneg (by norm_num) (by linarith))).le.trans_eq (add_comm _ _)
  have hh : logb 2 (2+B) ≤ 1+2*log B := by
    rw [logb, div_le_iff₀ (log_pos (by norm_num))]
    nlinarith only [hlog, mul_nonneg hL (show 0 ≤ log 2 - 1/2 by linarith [log_two_gt_d9])]
  push_cast
  nlinarith only [hh, hcl, hL, sq_nonneg (log B)]

/-- Uniform cost coefficient for one jet word. The largest workspace is
fourteen times the data width and the longest jet has height four times the short jet. -/
noncomputable def wordConstant (C β : ℝ) : ℝ :=
  4*14*8000000*(40 + 2*C*(1+logb 2 14)^β)

theorem wordConstant_nonneg {C β : ℝ} (hC : 0 ≤ C) : 0 ≤ wordConstant C β := by
  have h := logb_nonneg (by norm_num : (1:ℝ)<2) (by norm_num : 1 ≤ (14:ℝ))
  unfold wordConstant
  positivity

/-- Apply the explicit capacity and depth bounds of the prime and both endpoint words. -/
theorem stage_le {n e r h s v W D B : ℕ} {C β : ℝ} (hn : 0 < n)
    (hs : 0 < s) (hB : 6 ≤ B) (hβ : 0 ≤ β) (hC : 0 ≤ C) (hv : v ≤ n)
    (hW : 0 < W) (hcap : W ≤ 14*v) (hh : h ≤ 4*r)
    (hD : D ≤ 243*(84+6400*(1+Nat.clog 2 (2+B)))) :
    (D : ℝ)*(W*(40*e*h*convolutionEnvelope s) + (2*e*h)*(C*W*(1+logb 2 W)^β)) ≤
      wordConstant C β * (v*e*r) * rate n r s B β :=
  word_le hn hs hβ hC (by norm_num) (by norm_num) hv hW (by exact_mod_cast hcap) hh
    ((Nat.cast_le.mpr hD).trans (stage_depth hB))

/-- The exact price of either compiled prime conversion fits the common stage estimate. -/
theorem prime_word_le {n e r h s N B : ℕ} {C β : ℝ} (hn : 0 < n) (hs : 0 < s)
    (hB : 6 ≤ B) (hβ : 0 ≤ β) (hC : 0 ≤ C) (hN : 0 < N) (hNn : N ≤ n) (hh : h ≤ 4*r) :
    ConvolutionGrid.atTwoPrimeGridCost β C B N e h s ≤
      wordConstant C β*(N*e*r)*rate n r s B β := by
  simpa only [ConvolutionGrid.atTwoPrimeGridCost, Nat.cast_mul, Nat.cast_ofNat] using
    stage_le (e := e) (W := 14*N) hn hs hB hβ hC hNn (by positivity) le_rfl hh le_rfl

/-- Add the costs of the split summands using their disjoint data widths. -/
theorem sum_cost_le {ι : Type*} [Fintype ι] (cost width : ι → ℕ)
    {N : ℕ} {q : ℝ} (hcard : ∑ i, width i = N) (h : ∀ i, (cost i : ℝ) ≤ width i*q) :
    (∑ i, cost i : ℕ) ≤ (N:ℝ)*q := by
  rw [← hcard]
  push_cast
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => h i

/-- Combine the prime conversion with all the sector circuits in one
direction. Each sector performs a change of basis at each endpoint and a
Taylor shift between the two jet heights. -/
theorem transform_le {ι : Type*} [Fintype ι] {n e r s g prime N : ℕ} {B β C : ℝ}
    (w cost : ι → ℕ) (hwidth : ∑ i, w i = N)
    (hprime : (prime:ℝ) ≤ wordConstant C β*(N*e*r)*rate n r s B β)
    (hcost : ∀ i, (cost i:ℝ) ≤ (2*wordConstant C β+192)*(w i*e*r)*rate n r s B β)
    (hcomp : g ≤ prime + ∑ i, cost i) :
    (g:ℝ) ≤ (3*wordConstant C β+192)*(N*e*r)*rate n r s B β := by
  let W := wordConstant C β
  let Q := rate n r s B β
  have h := sum_cost_le cost w (q := (2*W+192)*e*r*Q) hwidth (fun i => (hcost i).trans_eq (by dsimp [W,Q]; ring))
  have hg : (g:ℝ) ≤ prime + (∑ i, cost i : ℕ) := by exact_mod_cast hcomp
  change (prime:ℝ) ≤ W*(N*e*r)*Q at hprime
  change (g:ℝ) ≤ (3*W+192)*(N*e*r)*Q
  linarith only [hg,hprime,h]

/-- After the forward and backward transforms have been compiled, charge the
gather and all point products. The resulting constant is uniform in the
choice of axes, extension degree, and jet length. -/
theorem packedCost_le {P : Finset ℕ} {n e a d g s : ℕ} {B β C : ℝ}
    (A : PrimeJetPacking P n e B) (hn : 0 < n) (he : 0 < e) (hes : e ≤ s)
    (hB : 1 ≤ B) (hC : 0 ≤ C)
    {ι : Type*} [Fintype ι] (H : ι → ℕ)
    (hcard : Fintype.card ι = ∏ p ∈ A.axes, p) (hH : ∀ i, H i ≤ 4*A.jet)
    (ha : (a:ℝ) ≤ C*((∏ p ∈ A.axes, p : ℕ)*e*A.jet)*rate n A.jet s B β)
    (hd : (d:ℝ) ≤ C*((∏ p ∈ A.axes, p : ℕ)*e*A.jet)*rate n A.jet s B β)
    (hg : g ≤ 2*a+d+e*A.jet*(∏ p ∈ A.axes, p) + ∑ i, JetAssembly.blockCost e (H i)) :
    (g:ℝ) ≤ A.widthWork (27*C+1305) β s := by
  let V := ∏ p ∈ A.axes, p
  let q := rate n A.jet s B β
  have hqr : convolutionEnvelope s ≤ q := envelope_le_rate hn (he.trans_le hes) hB
  have hq : 1 ≤ q := (convolutionEnvelope_one_le (he.trans_le hes)).trans hqr
  have hv : (V:ℝ)*e*A.jet ≤ 9*n := by exact_mod_cast A.volume_upper
  have hsum := JetAssembly.sum_blockCost_div_le_of_packing A hn he hes hcard H hH
  have hsum' := (div_le_iff₀ (by exact_mod_cast hn : 0<(n:ℝ))).mp hsum
  have hsumq := hsum'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hqr (by positivity : 0 ≤ 324*(4:ℝ))) (Nat.cast_nonneg n))
  have hvolq : (V:ℝ)*e*A.jet ≤ 9*n*q :=
    hv.trans (le_mul_of_one_le_right (by positivity) hq)
  have hab : C*((V:ℝ)*e*A.jet)*q ≤ C*(9*n)*q :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hC) (zero_le_one.trans hq)
  change (a:ℝ) ≤ C*((V:ℝ)*e*A.jet)*q at ha
  change (d:ℝ) ≤ C*((V:ℝ)*e*A.jet)*q at hd
  have hg' : (g:ℝ) ≤ 2*a+d+e*A.jet*(V:ℝ)+((∑ i, JetAssembly.blockCost e (H i) : ℕ):ℝ) := by
    exact_mod_cast hg
  change (g:ℝ) ≤ (27*C+1305)*n*(1+log B)^2*_
  rw [show (27*C+1305)*n*(1+log B)^2*
      ((1+logb 2 n)^β+(1+log (2+A.jet))*convolutionEnvelope s) =
      (27*C+1305)*n*q by unfold q rate; ring]
  norm_num at hsumq
  push_cast at hg'
  nlinarith only [hg', ha.trans hab, hd.trans hab, hvolq, hsumq]

end AtTwoCost

end FiniteFourier
end LinearAlgebra
end OAI
