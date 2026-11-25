import OAI.Computability.NearSquareRoot.IntegerBudget
import OAI.Computability.NearSquareRoot.PhysicalBoxPhase
import OAI.Computability.NearSquareRoot.PhysicalWalshSparseSweep
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetPhysical

/-! # Charging the full directed word to the original operand length

The per-row bound includes padded record volume, the fixed selected exponent,
and any fixed power of the logarithm of the address width. The actual number
of rows consumes one more logarithm. The ceiling in the primitive sweep clocks
and the final copy of the operand frame are included.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedLayer

open DigitPacking Filter ShortFourier.BatchWord PhysicalWalsh.Pieces
open SynchronizedPermutationBudget (layerClock)

noncomputable section

/-- Fixed-parameter time class for one physical row. -/
def RowClock (ρ : ℝ) (clock : ℕ → ℕ) : Prop := ∃ B : ℝ, 0 ≤ B ∧ ∃ l : ℕ,
  ∀ᶠ n in atTop, (clock n : ℝ) ≤ integerBudget B 0 ρ l 0 n

private def volumeTerm (ρ : ℝ) (n : ℕ) := (capacity n : ℝ)*addressBits n*(1+(addressBits n:ℝ))^ρ
private def logTerm (k : ℕ) := 1 + Real.log (2+(k:ℝ))

private theorem budget_eq (B ρ : ℝ) (l n : ℕ) :
    integerBudget B 0 ρ l 0 n = B*volumeTerm ρ n*(logTerm (addressBits n))^l := by
  unfold integerBudget volumeTerm logTerm
  ring

private theorem one_le_logTerm (k : ℕ) : 1 ≤ logTerm k := by
  unfold logTerm
  linarith [Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) k] : (1:ℝ) ≤ 2+k)]

private theorem volume_nonneg (ρ : ℝ) (n : ℕ) : 0 ≤ volumeTerm ρ n := by unfold volumeTerm; positivity

private theorem le_volume {ρ : ℝ} (hr : 0 ≤ ρ) {n : ℕ} (hn : 2 ≤ n) : (n : ℝ) ≤ volumeTerm ρ n := by
  have base : 1 ≤ (1+(addressBits n:ℝ))^ρ := Real.one_le_rpow (by linarith [Nat.cast_nonneg (α:=ℝ) (addressBits n)]) hr
  exact (show (n : ℝ) ≤ (capacity n:ℝ)*addressBits n by exact_mod_cast (packed_volume hn).1).trans
    (le_mul_of_one_le_right (by positivity) base)

private theorem clog_bound (k : ℕ) :
    (Nat.clog 2 (k+1):ℝ) ≤ (1+(Real.log 2)⁻¹)*logTerm k := by
  have h := clog_le_logScale (n:=k+1) (by omega)
  have hm : logScale (k+1) ≤ logTerm k := by
    unfold logScale logTerm
    push_cast
    apply add_le_add_right
    exact Real.log_le_log (by positivity) (by linarith)
  calc
    _ ≤ ((max 1 (Nat.clog 2 (k+1)):ℕ):ℝ) := by exact_mod_cast le_max_right 1 _
    _ ≤ _ := h.trans (mul_le_mul_of_nonneg_left hm (by positivity))

/-- The phase branch works for every operand width with at least two bits. -/
theorem phaseClock_le_budget {ρ : ℝ} (hr : 0 ≤ ρ) {n : ℕ} (hn : 2 ≤ n) :
    (phaseClock n:ℝ) ≤ integerBudget (2+(Real.log 2)⁻¹) 0 ρ 1 0 n := by
  rw [budget_eq, pow_one]
  unfold phaseClock
  push_cast
  have h := clog_bound (addressBits n)
  have e := one_le_logTerm (addressBits n)
  have he : (Nat.clog 2 (addressBits n+1):ℝ)+1 ≤ (2+(Real.log 2)⁻¹)*logTerm (addressBits n) := by linarith
  calc
    _ ≤ volumeTerm ρ n * ((2+(Real.log 2)⁻¹)*logTerm (addressBits n)) :=
      mul_le_mul (le_volume hr hn) he (by positivity) (volume_nonneg _ _)
    _ = _ := by ring

theorem phaseClock_bound {ρ : ℝ} (hr : 0 ≤ ρ) : RowClock ρ phaseClock :=
  ⟨_,by positivity,1,(eventually_ge_atTop (2:ℕ)).mono fun _ hn => phaseClock_le_budget hr hn⟩

/-- The physical Walsh clock includes the ceiling of the full address-array term. -/
theorem sparseTime_le_budget {ρ : ℝ} (hr : 0 ≤ ρ) {n : ℕ} (hn : 2 ≤ n) :
    (sparseTime ρ (addressBits n):ℝ) ≤ integerBudget 2 0 ρ 1 0 n := by
  rw [budget_eq, pow_one]
  let u := volumeTerm ρ n * logTerm (addressBits n)
  have hu : 1 ≤ u := by
    exact (show (1:ℝ) ≤ n by exact_mod_cast (show 1 ≤ n by omega)).trans
      ((le_volume hr hn).trans (le_mul_of_one_le_right (volume_nonneg _ _) (one_le_logTerm _)))
  have hceil := (Nat.ceil_lt_add_one (zero_le_one.trans hu)).le
  have eu : u = (2:ℝ)^addressBits n*addressBits n*(1+(addressBits n:ℝ))^ρ*logTerm (addressBits n) := by
    simp only [u,volumeTerm,capacity,Nat.cast_pow,Nat.cast_ofNat]
  change (⌈(2:ℝ)^addressBits n*addressBits n*(1+(addressBits n:ℝ))^ρ*logTerm (addressBits n)⌉₊:ℝ) ≤ _
  rw [←eu]
  dsimp only [u] at hceil hu ⊢
  linarith

theorem sparseTime_bound {ρ : ℝ} (hr : 0 ≤ ρ) : RowClock ρ (fun n => sparseTime ρ (addressBits n)) :=
  ⟨2, by norm_num, 1,(eventually_ge_atTop (2:ℕ)).mono fun _ hn => sparseTime_le_budget hr hn⟩

/-- The permutation clock uses the full physical volume allowance `n`. -/
theorem permutationClock_bound {ρ : ℝ} (hr : 0 ≤ ρ) :
    RowClock ρ (fun n => layerClock ρ (addressBits n) n) := by
  refine ⟨2,by norm_num,0,?_⟩
  filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
  rw [budget_eq,pow_zero,mul_one]
  have h : (n:ℝ)*(1+(addressBits n:ℝ))^ρ ≤ volumeTerm ρ n :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast (packed_volume hn).1) (by positivity)
  have hceil := (Nat.ceil_lt_add_one (by positivity : 0 ≤ (n:ℝ)*(1+(addressBits n:ℝ))^ρ)).le
  change (⌈(n:ℝ)*(1+(addressBits n:ℝ))^ρ⌉₊:ℝ) ≤ _
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  linarith [le_volume hr hn]

theorem RowClock.add {ρ : ℝ} {f g : ℕ → ℕ} (hf : RowClock ρ f) (hg : RowClock ρ g) :
    RowClock ρ (fun n => f n + g n) := by
  obtain ⟨B,b,l,fa⟩ := hf
  obtain ⟨D,d,m,ga⟩ := hg
  refine ⟨B+D,add_nonneg b d,max l m,?_⟩
  filter_upwards [fa,ga] with n fn gn
  rw [budget_eq] at fn gn ⊢
  push_cast
  have h := one_le_logTerm (addressBits n)
  calc
    _ ≤ B*volumeTerm ρ n*(logTerm (addressBits n))^(max l m) +
        D*volumeTerm ρ n*(logTerm (addressBits n))^(max l m) :=
      add_le_add (fn.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h (le_max_left _ _))
        (mul_nonneg b (volume_nonneg _ _)))) (gn.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ h (le_max_right _ _)) (mul_nonneg d (volume_nonneg _ _))))
    _ = _ := by ring

/-- A polynomial in the logarithm of the address width can count arbitrary
routing stages as well as scheduled Fourier rows. -/
theorem RowClock.mulCount {ρ D : ℝ} {clock count : ℕ → ℕ} (hc : RowClock ρ clock)
    (hD : 0 ≤ D) (d : ℕ)
    (countBound : ∀ᶠ n in atTop, (count n:ℝ) ≤ D*(1+Real.log (2+(addressBits n:ℝ)))^d) :
    RowClock ρ (fun n => count n * clock n) := by
  obtain ⟨B,b,l,ca⟩ := hc
  refine ⟨D*B,mul_nonneg hD b,d+l,?_⟩
  filter_upwards [countBound,ca] with n cn cl
  rw [budget_eq] at cl ⊢
  push_cast
  change (count n:ℝ) ≤ D*logTerm (addressBits n)^d at cn
  calc
    _ ≤ (D*logTerm (addressBits n)^d)*(B*volumeTerm ρ n*logTerm (addressBits n)^l) :=
      mul_le_mul cn cl (Nat.cast_nonneg _) (mul_nonneg hD (pow_nonneg (zero_le_one.trans (one_le_logTerm _)) _))
    _ = _ := by rw [pow_add]; ring

theorem RowClock.linear {ρ : ℝ} (hr : 0 ≤ ρ) : RowClock ρ id := by
  refine ⟨1,zero_le_one,0,?_⟩
  filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
  simpa only [budget_eq,one_mul,pow_zero,mul_one,id_eq] using le_volume hr hn

/-- A fixed polynomial setup in the address width is absorbed by the padded record array. -/
theorem RowClock.setup {ρ P : ℝ} (hr : 0 ≤ ρ) (hP : 0 ≤ P) (d : ℕ) {f : ℕ → ℕ}
    (setup : ∀ᶠ n in atTop, (f n:ℝ) ≤ P*(1+(addressBits n:ℝ))^d) : RowClock ρ f := by
  refine ⟨1,zero_le_one,0,?_⟩
  have h := addressBits_tendsto_atTop.eventually (eventually_polynomial_le_array_length P hP d)
  filter_upwards [setup,h,addressBits_tendsto_atTop.eventually_ge_atTop 1] with n fs hs hk
  rw [budget_eq,pow_zero,mul_one,one_mul]
  have cap : P*(1+(addressBits n:ℝ))^d ≤ (capacity n:ℝ) := by
    simpa only [capacity,Nat.cast_pow,Nat.cast_ofNat] using hs
  have hbase := Real.one_le_rpow (by linarith [Nat.cast_nonneg (α:=ℝ) (addressBits n)] :
    1 ≤ 1+(addressBits n:ℝ)) hr
  exact ((fs.trans cap).trans (le_mul_of_one_le_right (Nat.cast_nonneg _) (by exact_mod_cast hk))).trans
    (le_mul_of_one_le_right (by positivity) hbase)

/-- A sum clock can uniformly cover the three physical opcode branches. -/
theorem combinedClock_bound {ρ : ℝ} (hr : 0 ≤ ρ) {perm : ℕ → ℕ} (route : RowClock ρ perm) :
    RowClock ρ (fun n => perm n + phaseClock n + sparseTime ρ (addressBits n)) :=
  (route.add (phaseClock_bound hr)).add (sparseTime_bound hr)

private theorem depth_le (k : ℕ) :
    (3*boxDepth k : ℕ) ≤ (936230400*(1+(Real.log 2)⁻¹)+117074160)*logTerm k := by
  have hd : 3*boxDepth k = 936230400*Nat.clog 2 k+117074160 := by unfold boxDepth BoxScale.width; ring
  rw [hd]
  push_cast
  have h : (Nat.clog 2 k:ℝ) ≤ Nat.clog 2 (k+1) := by exact_mod_cast Nat.clog_mono_right 2 (Nat.le_succ k)
  have hb := h.trans (clog_bound k)
  have ho := one_le_logTerm k
  linarith

theorem RowClock.transform {ρ : ℝ} (hr : 0 ≤ ρ) {clock : ℕ → ℕ} (hc : RowClock ρ clock) :
    RowClock ρ (fun n => 3*boxDepth (addressBits n)*clock n+n) :=
  (hc.mulCount (D:=936230400*(1+(Real.log 2)⁻¹)+117074160) (by positivity) 1
    (Filter.Eventually.of_forall fun n => by simpa only [pow_one,logTerm] using depth_le (addressBits n))).add
    (RowClock.linear hr)

theorem RowClock.eventually_le {ρ γ : ℝ} (hr : 0 ≤ ρ) (hγ : ρ < γ) {clock : ℕ → ℕ}
    (hc : RowClock ρ clock) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, (clock n:ℝ) ≤ C*n*logScale n^γ := by
  obtain ⟨B,b,l,ca⟩ := hc
  obtain ⟨K,hK,leK⟩ := eventually_integerBudget_le b (P:=0) le_rfl hr hγ l 0
  exact ⟨K,hK,ca.and leK |>.mono fun _ ⟨h,h'⟩ => h.trans h'⟩

theorem transformClock_eventually_le {ρ γ B : ℝ} (hr : 0 ≤ ρ) (hγ : ρ < γ) (hB : 0 ≤ B)
    (l : ℕ) (clock : ℕ → ℕ) (cost : ∀ᶠ n in atTop, (clock n:ℝ) ≤ integerBudget B 0 ρ l 0 n) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, (3*boxDepth (addressBits n)*clock n+n:ℕ) ≤ C*n*logScale n^γ :=
  ((RowClock.transform hr ⟨B,hB,l,cost⟩).eventually_le hr hγ)

end
end FixedLayer

end NearSquareRoot
end Computability
end OAI
