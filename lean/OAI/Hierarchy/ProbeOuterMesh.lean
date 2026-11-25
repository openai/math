import OAI.Hierarchy.ProbeFeed
import OAI.Hierarchy.ProbeLedger
import OAI.Hierarchy.ProbeCooling

namespace OAI
/-! # Physical injection and cooling increments on a fixed outer mesh -/

namespace Hierarchy.AdaptiveProbe

open scoped BigOperators
noncomputable section

/-- Every payload is injected in the same whole-bit slices. Their normalized
sum is exactly one, even when the width is not a multiple of the mesh size. -/
def payloadSlice (steps w j : ℕ) : ℝ := (slice steps w j:ℝ)/w

theorem payloadSlice_sum {steps w : ℕ} (hm : 0<steps) (hw : 0<w) :
    ∑ j ∈ Finset.range steps, payloadSlice steps w j=1 := by
  simp only [payloadSlice,←Finset.sum_div,←Nat.cast_sum]
  rw [slice_sum steps w hm,div_self (by positivity)]

theorem payloadSlice_bounds {steps w : ℕ} (hm : 0<steps) (hw : steps≤w) (j : ℕ) :
    0≤payloadSlice steps w j ∧ payloadSlice steps w j≤2/steps := by
  have sw : (0:ℝ)<w := by exact_mod_cast hm.trans_le hw
  have ss : (0:ℝ)<steps := by exact_mod_cast hm
  have rat : (steps:ℝ)≤w := by exact_mod_cast hw
  have error := (abs_lt.mp (slice_error steps w j hm)).2
  dsimp [payloadSlice]
  refine ⟨by positivity,(div_le_iff₀ sw).mpr ?_⟩
  have q : 1≤(w:ℝ)/steps := (le_div_iff₀ ss).mpr (by linarith)
  calc
    (slice steps w j:ℝ) ≤ (w:ℝ)/steps+1 := by linarith
    _ ≤ (2/steps)*w := by nlinarith [show (2/(steps:ℝ))*w=2*(w/steps) by ring]

/-- The physical monotone time mesh lands at the prescribed positive final time. -/
def clockTime (s₀ : ℝ) (steps j : ℕ) := 1-(j:ℝ)/steps*(1-s₀)

theorem clock_endpoints {s₀ : ℝ} {steps : ℕ} (hm : 0<steps) :
    clockTime s₀ steps 0=1 ∧ clockTime s₀ steps steps=s₀ := by
  have ne : (steps:ℝ)≠0 := by positivity
  simp [clockTime,ne]

theorem clock_bounds {s₀ : ℝ} {steps : ℕ} (_hs : 0<s₀) (leOne : s₀≤1) (hm : 0<steps)
    (j : ℕ) (hj : j≤steps) : s₀≤clockTime s₀ steps j ∧ clockTime s₀ steps j≤1 := by
  have ss : (0:ℝ)<steps := by exact_mod_cast hm
  have rat : (j:ℝ)/steps≤1 := (div_le_iff₀ ss).2 (by exact_mod_cast (by simpa using hj : j≤1*steps))
  have nn : 0≤(j:ℝ)/steps := by positivity
  unfold clockTime
  constructor <;> nlinarith [mul_nonneg nn (sub_nonneg.mpr leOne),
    mul_nonneg (sub_nonneg.mpr rat) (sub_nonneg.mpr leOne)]

theorem clock_drop (s₀ : ℝ) (steps j : ℕ) :
    clockTime s₀ steps j-clockTime s₀ steps (j+1)=(1-s₀)/steps := by
  unfold clockTime
  push_cast
  ring

variable {I : Type*} [Fintype I]

/-- Injection is evaluated at the true maximizer on the current stock; the
same proof handles a crude box bound or the tighter low-excess bound. -/
theorem outer_inject (b A z payload : I → ℝ) {a M q L V : ℝ}
    (ha : 0<a) (hb : ∀ i,0≤b i) (hM : 0≤M) (hz : ∀ i,0≤z i) (hA : ∀ i,0≤A i)
    (pay : ∀ i,0≤payload i) (hq : 0≤q)
    (offer : pairing payload (maximizer a M 1 b A z)≤L) (square : ∑ i, payload i^2 ≤V) :
    potential a M 1 b A (fun i=>z i+q*payload i) ≤ potential a M 1 b A z+
      q*L+q^2*V/(4*a) := by
  have up := potential_increment (s:=1) (s':=1) b A z (fun i=>q*payload i)
    ha hb hM (by norm_num) (by norm_num) hz (fun i=>add_nonneg (hz i) (mul_nonneg hq (pay i))) hA
  have lin : pairing (fun i=>q*payload i) (maximizer a M 1 b A z) =
      q*pairing payload (maximizer a M 1 b A z) := by simp [pairing,Finset.mul_sum,mul_assoc]
  have err : ∑ i, (q*payload i)^2/(4*a) = q^2*(∑ i,payload i^2)/(4*a) := by
    simp [mul_pow,Finset.mul_sum,Finset.sum_div]
  simp only [sub_self,zero_mul,sub_zero,mul_one,lin,err] at up
  exact up.trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left offer hq))
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left square (sq_nonneg _)) (by positivity)))

/-- The quadratic loss in a downward time increment uses the square norm of
the old gradient and the positive lower endpoint of the mesh. -/
theorem outer_cool (b A z : I → ℝ) {a M s s' s₀ L V : ℝ}
    (ha : 0<a) (hb : ∀ i,0≤b i) (hM : 0≤M) (hz : ∀ i,0≤z i) (hA : ∀ i,0≤A i)
    (h₀ : 0<s₀) (lower : s₀≤s') (dec : s'≤s)
    (value : score a M b (maximizer a M s b A z)≤L)
    (gradient : ∑ i, (rowSlope a (b i) M (maximizer a M s b A z i))^2≤V) :
    potential a M s' b A z ≤ potential a M s b A z+(s-s')*L+(s-s')^2*V/(4*s₀*a) := by
  let x := maximizer a M s b A z
  have newpos := h₀.trans_le lower
  have up := potential_increment (s:=s) (s':=s') b A z (fun _=>0)
    ha hb hM (newpos.trans_le dec) newpos hz (fun i=>by simpa using hz i) hA
  have neg : s'-s= -(s-s') := by ring
  have err : (∑ i, ((s-s')*rowSlope a (b i) M (x i))^2/(4*s'*a)) =
      (s-s')^2*(∑ i,(rowSlope a (b i) M (x i))^2)/(4*s'*a) := by
    simp [mul_pow,Finset.mul_sum,Finset.sum_div]
  have den : 0<4*s₀*a := by positivity
  have denom : 4*s₀*a≤4*s'*a := by gcongr
  have sq : 0≤∑ i,(rowSlope a (b i) M (x i))^2 := Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have zp : pairing (fun _ : I => (0:ℝ)) x=0 := by simp [pairing]
  simp only [zp,add_zero,zero_add,neg,neg_mul,sub_neg_eq_add,show maximizer a M s b A z=x from rfl,err] at up
  exact up.trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left value (sub_nonneg.mpr dec)))
    ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left gradient (sq_nonneg _)) (by positivity)).trans
      (div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) (sq.trans gradient)) den denom)))

end
end Hierarchy.AdaptiveProbe

end OAI
