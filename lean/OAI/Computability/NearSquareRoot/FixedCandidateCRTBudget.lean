import OAI.Computability.NearSquareRoot.FixedCandidateCRTSweep
import OAI.Computability.NearSquareRoot.CRTPositionClock
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetRate
import OAI.Computability.NearSquareRoot.IntegerBudget
import OAI.Computability.NearSquareRoot.PhysicalWalshRouterClock

/-! # The whole CRT sweep on the multiplication record array

At every tree depth the program emits two switch directions for each bit of
the common width. Every switch stage partitions its targets into guarded
batches. Each batch pays for two position permutations and one masked row
pass. The two fixed-point components use two equal-width signed bit strings.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTBudget

open Filter DigitPacking Controlled PositionProgram
open SynchronizedPermutationBudget (rowFactor row_factor_time)

/-- An upper bound for both the physical guard stride and the widest axis. -/
def stride (k : ℕ) := max (Controlled.guardWidth k) (BoxScale.width k)

/-- One quarter of the address bits is available even after retaining every
external control of the balanced node layer. -/
def batches (k : ℕ) := Controlled.batchCount (CoprimeBox.box k).length k 4 (stride k)

/-- Each packed bit row consists of both signed fixed-point component words. -/
def volume (n : ℕ) := capacity n * (2 * (FixedPoint.componentBits (addressBits n) + 1))

/-- Forward position preparation, the mask stage, reverse position routing,
and a linear row-copy allowance. -/
noncomputable def batchClock (ρ : ℝ) (k V : ℕ) : ℕ :=
  V * (2*(positionFactor ρ k+1) + (rowFactor k ρ+1) + 1)

/-- Each stage permits a polynomial amount of setup for each batch. The extra
batch allowance covers the stage's initial and final copies. -/
noncomputable def stageClock (ρ : ℝ) (deg n : ℕ) :=
  let k := addressBits n
  (batches k + 1) * (batchClock ρ k (volume n) + (k+1)^deg)

/-- This is the literal clock returned by executing the fixed-candidate CRT
forest with the bounded native bit-row command at each switch stage. -/
noncomputable def routeClock (ρ : ℝ) (deg n : ℕ) :=
  CRTStream.count n * (stageClock ρ deg n + n) + n

theorem volume_le (n : ℕ) (hk : 1 ≤ addressBits n) :
    volume n ≤ 202*(capacity n * addressBits n) := by
  have h : 2*(FixedPoint.componentBits (addressBits n)+1) ≤ 202*addressBits n := by
    unfold FixedPoint.componentBits; omega
  exact (Nat.mul_le_mul_left (capacity n) h).trans (le_of_eq (by ac_rfl))

/-- The full swept bit arena, including padding, is linear in input length. -/
theorem volume_le_linear {n : ℕ} (hn : 2 ≤ n) : volume n ≤ 9696*n := by
  have hk : 1 ≤ addressBits n := by
    have := width_pos hn; have := width_le_twice_addressBits hn; omega
  calc
    _ ≤ 202*(capacity n * addressBits n) := volume_le n hk
    _ ≤ 202*(48*n) := Nat.mul_le_mul_left _ (packed_volume hn).2
    _ = _ := by ring

theorem input_le_volume {n : ℕ} (hn : 2 ≤ n) : n ≤ volume n := by
  apply (packed_volume hn).1.trans
  change capacity n * addressBits n ≤ capacity n * (2 * (FixedPoint.componentBits (addressBits n) + 1))
  exact Nat.mul_le_mul_left _ (by unfold FixedPoint.componentBits; omega)

private theorem setup_fits (deg : ℕ) : ∀ᶠ n : ℕ in atTop, (addressBits n+1)^deg ≤ volume n := by
  filter_upwards [addressBits_tendsto_atTop.eventually
    (eventually_polynomial_le_array_length 1 zero_le_one deg)] with n hn
  have h : (addressBits n+1)^deg ≤ capacity n := by
    change 1*(1+(addressBits n:ℝ))^deg ≤ (2:ℝ)^addressBits n at hn
    rw [one_mul,add_comm] at hn
    exact_mod_cast hn
  exact h.trans <| Nat.le_mul_of_pos_right _ (by unfold FixedPoint.componentBits; positivity)

/-- On good reserve guesses the arena includes at most a fixed polynomial
in the address width alongside the array. The forest also retains the
original input-length frame. -/
theorem eventually_linear_arena (C deg : ℕ) {A : ℕ → ℕ}
    (good : ∀ᶠ n in atTop, A n ≤ C * (volume n + (addressBits n+1)^deg)) :
    ∀ᶠ n in atTop, n + A n ≤ (1+19392*C)*n := by
  filter_upwards [good,setup_fits deg,eventually_ge_atTop (2:ℕ)] with n h hs hn
  have bound := volume_le_linear hn
  calc
    _ ≤ n+C*(9696*n+9696*n) := by gcongr; exact h.trans (by gcongr; exact hs.trans bound)
    _ = _ := by ring

private def L (k : ℕ) := 1 + Nat.clog 2 (k+1)

private theorem stride_bound (k : ℕ) : stride k ≤ 20*L k := by
  have h : Nat.clog 2 k ≤ Nat.clog 2 (k+1) := Nat.clog_mono_right 2 (Nat.le_succ k)
  simp only [stride, max_le_iff, Controlled.guardWidth, BoxScale.width, L]
  omega

private theorem eventually_room : ∀ᶠ k : ℕ in atTop, 8*4*stride k ≤ k := by
  filter_upwards [Controlled.eventually_clog_fits 1280,eventually_ge_atTop (1:ℕ)] with k h hk
  have pos := Nat.clog_pos (by decide : 1 < 2) (show 1 < k+1 by omega)
  have hs := stride_bound k
  unfold L at hs; omega

/-- For any fixed pair of reserve degrees, a sufficiently large actual box
has room for the batch guards, both reserves, and the external CRT controls
at every depth. -/
theorem eventually_layout_room (low high : ℕ) :
    ∀ᶠ k in atTop, 8*4*stride k ≤ k ∧ payloadBits low k + payloadBits high k ≤ k/16 ∧
      ∀ t, ((CRTTree.controls t (CoprimeBox.box k)).map Prod.fst).sum + k/4 ≤ k := by
  obtain ⟨K, valid⟩ := CoprimeBox.eventually_valid
  filter_upwards [eventually_room,Controlled.eventually_batch_reserves 4 low high,
    Controlled.eventually_clog_fits 40,eventually_ge_atTop K] with k room res wide hk
  refine ⟨room, res.2.trans (by omega), fun t => ?_⟩
  have hlog := Nat.clog_mono_right 2 (show k ≤ k+1 by omega)
  have half : 2*BoxScale.width k ≤ k := by unfold BoxScale.width; omega
  have frac := CRTTree.controlFraction (valid k hk) t half
  omega

private theorem length_le_sum (xs : List ℕ) (h : ∀ x ∈ xs, 0 < x) : xs.length ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    simp only [List.length_cons,List.sum_cons]; omega

theorem axis_count {k : ℕ} (valid : BoxShape.Valid k (BoxScale.width k) (CoprimeBox.box k)) :
    (CoprimeBox.box k).length ≤ k := by
  apply le_trans _ valid.widthSum.le
  simpa only [List.length_map] using length_le_sum ((CoprimeBox.box k).map Prod.fst)
    (fun j hj => by obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hj; exact (valid.axisBounds _ hq).1)

theorem pass_count {n : ℕ} (valid : Directory n) (room : 8*4*stride (addressBits n) ≤ addressBits n) :
    (CRTStream.count n+1)*(batches (addressBits n)+2) ≤
      (41*1282)*(1+Nat.clog 2 (addressBits n+1))^3 := by
  let k := addressBits n
  have hd := axis_count valid
  have levels : Nat.clog 2 (box n).length ≤ Nat.clog 2 (k+1) := Nat.clog_mono_right 2 (hd.trans (Nat.le_succ _))
  have width : Nat.clog 2 k ≤ Nat.clog 2 (k+1) := Nat.clog_mono_right 2 (Nat.le_succ k)
  have hs := stride_bound k
  have pos : 0 < stride k := by
    unfold stride Controlled.guardWidth; omega
  have hb : batches k ≤ 16*4*stride k := Controlled.batch_count_le (j:=4) (g:=stride k) (by decide) pos hd room
  have levels' : Nat.clog 2 (box n).length ≤ L k := by unfold L; omega
  have width' : 2*BoxScale.width k ≤ 40*L k := by unfold BoxScale.width L; omega
  have hn : CRTStream.count n+1 ≤ 41*(L k)^2 := by
    have h := Nat.mul_le_mul levels' width'
    change Nat.clog 2 (box n).length * (2*BoxScale.width k) + 1 ≤ _
    have hlo : 1 ≤ (L k)^2 := Nat.one_le_pow _ _ (by unfold L; omega)
    nlinarith only [h,hlo]
  have hbatch : batches k+2 ≤ 1282*L k := by
    have hlo : 1 ≤ L k := by unfold L; omega
    omega
  exact (Nat.mul_le_mul hn hbatch).trans (by change _ ≤ (41*1282)*(L k)^3; ring_nf; rfl)

/-- Concrete bound on a full preparation-mask-restoration pass. -/
theorem batch_charge (k V : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ((batchClock ρ k V + V : ℕ) : ℝ) ≤ 14*(V:ℝ)*positionRate ρ k := by
  have hp := positionFactor_time hρ k
  have hm := row_factor_time k hρ
  have one := one_le_positionRate hρ k
  have major : ((k:ℝ)+1)^ρ ≤ positionRate ρ k := by
    unfold positionRate; push_cast
    exact le_mul_of_one_le_left (by positivity) (by linarith [Nat.cast_nonneg (α:=ℝ) (Nat.clog 2 (k + 1))])
  unfold batchClock
  push_cast
  have f : 2*((positionFactor ρ k:ℝ)+1)+((rowFactor k ρ:ℝ)+1)+1+1 ≤ 14*positionRate ρ k := by
    linarith
  nlinarith only [mul_le_mul_of_nonneg_left f (Nat.cast_nonneg (α:=ℝ) V)]

private theorem clock_bound {ρ : ℝ} (deg : ℕ) {n : ℕ} (hn : 2 ≤ n)
    (setup : (addressBits n+1)^deg ≤ volume n) :
    routeClock ρ deg n ≤ (CRTStream.count n+1)*(batches (addressBits n)+2)*
      (batchClock ρ (addressBits n) (volume n)+volume n) := by
  let V := volume n
  let B := batchClock ρ (addressBits n) V
  let b := batches (addressBits n)
  have hv : n ≤ V := input_le_volume hn
  have hs : stageClock ρ deg n + n ≤ (b+2)*(B+V) := by
    calc
      _ ≤ (b+1)*(B+V) + (B+V) := by
        unfold stageClock; dsimp only
        exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.add_le_add_left setup _)) (by omega)
      _ = _ := by ring
  calc
    _ ≤ CRTStream.count n*((b+2)*(B+V)) + (b+2)*(B+V) := by
      unfold routeClock
      exact Nat.add_le_add (Nat.mul_le_mul_left _ hs)
        (hv.trans ((by omega : V ≤ B+V).trans (Nat.le_mul_of_pos_left _ (by omega))))
    _ = _ := by ring

/-- The padded array costs four logarithmic factors in the address width:
three from the complete batch count, and one from position routing. -/
theorem routeClock_integerBudget {ρ : ℝ} (hρ : 0 ≤ ρ) (deg : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      (routeClock ρ deg n : ℝ) ≤ integerBudget C 0 ρ 4 0 n := by
  let b : ℝ := 2 + (Real.log 2)⁻¹
  let G : ℝ := 41*1282
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨cut, valid⟩ := CoprimeBox.eventually_valid
  refine ⟨G*14*202*b^4,by dsimp [G]; positivity,?_⟩
  filter_upwards [eventually_ge_atTop (2:ℕ),addressBits_tendsto_atTop.eventually_ge_atTop cut,
    addressBits_tendsto_atTop.eventually eventually_room,setup_fits deg] with n hn hvalid room setup
  let k := addressBits n
  have hk : 1 ≤ k := by
    have := width_pos hn; have := width_le_twice_addressBits hn; dsimp [k]; omega
  have vr : (volume n:ℝ) ≤ 202*((capacity n:ℝ)*k) := by exact_mod_cast volume_le n hk
  have hr := clock_bound (ρ:=ρ) deg hn setup
  have count := pass_count (valid _ hvalid) room
  have hc : (routeClock ρ deg n:ℝ) ≤ (G*(L k:ℝ)^3) * (batchClock ρ k (volume n)+volume n:ℕ) := by
    dsimp only [G]
    exact_mod_cast hr.trans (Nat.mul_le_mul_right _ count)
  let log := 1+Real.log (2+(k:ℝ))
  have one : 1 ≤ log := PhysicalWalshNode.RouterClock.one_le_logWidth k
  have l : (L k:ℝ) ≤ b*log := by
    have cl := PhysicalWalshNode.RouterClock.clog_logWidth k
    unfold PhysicalWalshNode.RouterClock.logWidth at cl
    unfold L; push_cast; dsimp only [b,log]; linarith only [cl,one]
  calc
    _ ≤ (G*(L k:ℝ)^3) * (14*(volume n:ℝ)*positionRate ρ k) :=
      hc.trans (mul_le_mul_of_nonneg_left (batch_charge k _ hρ) (by dsimp [G]; positivity))
    _ ≤ (G*(b*log)^3) * (14*(202*((capacity n:ℝ)*k))*((b*log)*(1+(k:ℝ))^ρ)) := by
      unfold positionRate
      rw [show ((1+Nat.clog 2 (k+1):ℕ):ℝ) = (L k:ℝ) by rfl,
        Nat.cast_add_one, add_comm (k:ℝ) 1]
      gcongr
    _ = _ := by simp only [integerBudget, zero_mul, add_zero]; dsimp [log,k]; ring

/-- Each fixed routing exponent below the target exponent yields one uniform
bound in the operand length, in either routing direction. -/
theorem routeClock_asymptotic {ρ γ : ℝ} (hρ : 0 ≤ ρ) (gap : ρ < γ) (deg : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, (routeClock ρ deg n:ℝ) ≤ K*n*logScale n^γ := by
  obtain ⟨C,hC,clock⟩ := routeClock_integerBudget hρ deg
  obtain ⟨K,hK,h⟩ := eventually_integerBudget_le hC.le (le_refl 0) hρ gap 4 0
  exact ⟨K,hK,clock.and h |>.mono fun _ p => p.1.trans p.2⟩

/-- One strictly intermediate routing exponent suffices for a requested
near-square-root bound, including all positive values of the slack. -/
theorem routeClock_epsilon {ε : ℝ} (hε : 0 < ε) (deg : ℕ) :
    ∃ ρ : ℝ, 1/2 < ρ ∧ ρ < 1 ∧ ∃ K : ℝ, 0 < K ∧
      ∀ᶠ n in atTop, (routeClock ρ deg n : ℝ) ≤ K*n*logScale n^(1/2+ε) := by
  let ρ : ℝ := 1/2 + min (ε/2) (1/4)
  have lower : 1/2 < ρ := lt_add_of_pos_right _ (lt_min (by linarith) (by norm_num))
  have upper : ρ < 1 := by dsimp [ρ]; linarith [min_le_right (ε/2) (1/4:ℝ)]
  refine ⟨ρ,lower,upper,routeClock_asymptotic (by linarith) ?_ deg⟩
  dsimp [ρ]; linarith [min_le_left (ε/2) (1/4:ℝ)]

end FixedCandidate.CRTBudget

end NearSquareRoot
end Computability
end OAI
