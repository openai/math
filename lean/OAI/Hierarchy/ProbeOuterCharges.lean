import OAI.Hierarchy.ProbeOuterRates

namespace OAI
/-! # The two finite phases of the signed probe account -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators
noncomputable section

/-- The time is one throughout the injection, then follows the cooling mesh. -/
def phaseTime (s₀ : ℝ) (m j : ℕ) := clockTime s₀ m (j-m)

/-- A sum over both phases, with the cooling cursor starting at zero. -/
def phaseCharge (m : ℕ) (inject cool : ℕ → ℝ) (j : ℕ) :=
  if j<m then inject j else cool (j-m)

theorem phaseCharge_sum (m : ℕ) (inject cool : ℕ → ℝ) :
    ∑ j ∈ Finset.range (m+m), phaseCharge m inject cool j =
      (∑ j ∈ Finset.range m, inject j)+(∑ j ∈ Finset.range m, cool j) := by
  rw [Finset.sum_range_add]
  congr 1
  · exact Finset.sum_congr rfl (fun j hj=>by simp [phaseCharge,Finset.mem_range.mp hj])
  · exact Finset.sum_congr rfl (fun j _=>by simp [phaseCharge])

def regularCharge (m w : ℕ) (s₀ r scale : ℝ) := phaseCharge m
  (fun j=> 2*payloadSlice m w j)
  (fun j=> (1-s₀)/(m:ℝ)*(scale*min (1/clockTime s₀ m j) (1/r)+1))

def crudeCharge (m w : ℕ) (s₀ C D : ℝ) := phaseCharge m
  (fun j=>payloadSlice m w j*(C+1/2)) (fun _=>(1-s₀)/(m:ℝ)*(D+1/2))

theorem regular_spend {m w : ℕ} {s₀ r scale : ℝ} (hm : 0<m) (hw : 0<w) (hs : 0<s₀)
    (hs₁ : s₀≤1) (hr : 0<r) (hr₁ : r≤1) (nn : 0≤scale) (intg : scale*(1-Real.log r)≤1) :
    (∑ j ∈ Finset.range (m+m),regularCharge m w s₀ r scale j)≤4 := by
  rw [regularCharge,phaseCharge_sum,←Finset.mul_sum,payloadSlice_sum hm hw,mul_one]
  linarith [outer_cooling_sum hm hs hs₁ hr hr₁ nn intg]

theorem crude_spend {m w : ℕ} {s₀ C D : ℝ} (hm : 0<m) (hw : 0<w) (hs : 0<s₀) (hD : 0≤D) :
    (∑ j ∈ Finset.range (m+m),crudeCharge m w s₀ C D j)≤C+D+1 := by
  have sm : (0:ℝ)<m := by exact_mod_cast hm
  rw [crudeCharge,phaseCharge_sum,←Finset.sum_mul,payloadSlice_sum hm hw,one_mul]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have eq : (m:ℝ)*((1-s₀)/(m:ℝ)*(D+1/2))=(1-s₀)*(D+1/2) := by field_simp
  rw [eq]
  nlinarith only [mul_nonneg hs.le (show 0≤D+1/2 by linarith)]

variable {I : Type*} [Fintype I]

/-- Both the low-excess and unconditional box bound use this same estimate
for the whole-bit injection. All constants are per payload. -/
theorem inject_scaled {n m w : ℕ} (hm : 0<m) (hw : m≤w) (j : ℕ) (b A z u : I→ℝ)
    {a M C L : ℝ} (ha : 0<a) (hb : ∀ i,0≤b i) (hM : 0≤M) (hz : ∀ i,0≤z i)
    (hA : ∀ i,0≤A i) (hu : ∀ i,0≤u i) (hC : 0≤C) (large : C≤a*m)
    (sumSq : (∑ i,u i^2)≤C*n) (offer : pairing u (maximizer a M 1 b A z)≤L*n) :
    potential a M 1 b A (fun i=>z i+payloadSlice m w j*u i) ≤
      potential a M 1 b A z+payloadSlice m w j*(L+1/2)*n := by
  let q := payloadSlice m w j
  have qp : 0≤q := (payloadSlice_bounds hm hw j).1
  have qc : q*C≤2*(1*a) := by simpa using injected_curvature (j:=j) hm hw hC ha large
  have err := mesh_quadratic (s:=1) (V:=∑ i,u i^2) (n:=(n:ℝ))
    (by simpa using ha) qp (by positivity) sumSq qc
  have up := outer_inject b A z u ha hb hM hz hA hu qp offer (le_refl (∑ i,u i^2))
  dsimp only [q] at *
  simp only [mul_one] at err
  nlinarith only [up,err]

theorem cool_scaled {n m : ℕ} (hm : 0<m) (j : ℕ) (hj : j<m) (b A z : I→ℝ)
    {a M s₀ G L : ℝ} (ha : 0<a) (hb : ∀ i,0≤b i) (hM : 0≤M) (hz : ∀ i,0≤z i)
    (hA : ∀ i,0≤A i) (hs : 0<s₀) (hs₁ : s₀≤1) (hG : 0≤G) (large : G≤s₀*a*m)
    (sumSq : (∑ i,(rowSlope a (b i) M (maximizer a M (clockTime s₀ m j) b A z i))^2)≤G*n)
    (scoreBound : score a M b (maximizer a M (clockTime s₀ m j) b A z)≤L*n) :
    potential a M (clockTime s₀ m (j+1)) b A z ≤
      potential a M (clockTime s₀ m j) b A z+(1-s₀)/(m:ℝ)*(L+1/2)*n := by
  let δ := clockTime s₀ m j-clockTime s₀ m (j+1)
  have drop : δ=(1-s₀)/(m:ℝ) := clock_drop s₀ m j
  have dp : 0≤δ := drop ▸ div_nonneg (sub_nonneg.mpr hs₁) (by positivity)
  have endLe := (clock_bounds hs hs₁ hm (j+1) (by omega)).1
  have big := cooled_curvature (j:=j) hm hs hs₁ hG ha large
  have err := mesh_quadratic (V:=_) (mul_pos hs ha) dp (by positivity : 0≤(n:ℝ)) sumSq big
  have up := outer_cool b A z ha hb hM hz hA hs endLe (sub_nonneg.mp dp) scoreBound
    (le_refl (∑ i,(rowSlope a (b i) M (maximizer a M (clockTime s₀ m j) b A z i))^2))
  dsimp only [δ] at *
  rw [clock_drop] at err up
  nlinarith only [up,err]

end
end Hierarchy.AdaptiveProbe

end OAI
