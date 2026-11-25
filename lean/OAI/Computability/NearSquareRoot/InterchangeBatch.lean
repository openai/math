import OAI.Computability.NearSquareRoot.InterchangeLabelBudget
import OAI.Computability.NearSquareRoot.InterchangeRecurrence
import OAI.Computability.NearSquareRoot.KernelSwapRepair

/-!
# Selecting constants for the batched interchange

The support matrix, incident rectangles, rational address coordinates and
binary spectral-repair rows are all those of the implemented constructions.
Both the bound on the main calls and the reserve contraction use the same
dyadic alphabet. A coefficient of the repair extension carries a full batch
of independent ground-field components.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

open Filter OAI.LinearAlgebra.FiniteFourier

/-- Every coefficient in the repair row stores a full power basis. -/
noncomputable abbrev componentWidth (m : ℕ) := Fintype.card (SwapRepair.BasisIndex m)

noncomputable abbrev independentRows (m : ℕ) := SwapRepair.width m * componentWidth m
noncomputable abbrev correctedRows (m : ℕ) := SwapRepair.checks m * componentWidth m

private theorem independentRows_pos (m : ℕ) : 0 < independentRows m := by
  simp only [independentRows, componentWidth, SwapRepair.width, SwapRepair.BasisIndex,
    primePredictorRows, Fintype.card_fin, countPencilOrder]
  positivity

private theorem correctedRows_le (m : ℕ) : 2 * m^3 * correctedRows m ≤ independentRows m := by
  change 2 * m^3 * (SwapRepair.checks m * componentWidth m) ≤ _
  rw [← mul_assoc, Nat.mul_comm (2*m^3)]
  exact Nat.mul_le_mul_right _ (Nat.div_mul_le_self ..)

private theorem order_time (m : ℕ) (hm : 2 ≤ m) :
    ((4 * SwapRepair.order m : ℕ) : ℝ) ≤ 80 * Real.sqrt (m*(1+Real.log m)) := by
  have hm' : 1 ≤ (m : ℝ) := by exact_mod_cast hm.trans' (by decide : 1 ≤ 2)
  have hmpos : 0 < (m : ℝ) := zero_lt_one.trans_le hm'
  have hlog : Real.log (2*m) ≤ 1+Real.log m := by
    rw [Real.log_mul (by norm_num) hmpos.ne']
    linarith [Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ))]
  have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlog hmpos.le)
  have hs1 : 1 ≤ Real.sqrt (m*(1+Real.log m)) := by
    simpa using (Real.sqrt_le_sqrt (one_le_mul_of_one_le_of_one_le hm'
      (by linarith [Real.log_nonneg hm'] : 1 ≤ 1+Real.log m)))
  have h := SwapRepair.pencil_stages_le hm
  push_cast
  linarith

private theorem reserve_contraction {p : ℕ} (hp : 0 < p) {α γ : ℝ} (hag : γ < α)
    (hg : 1/2 + (3*p-1)/(p:ℝ)^2 < γ) :
    ∀ᶠ m : ℕ in atTop, ∀ k : ℕ, (2:ℝ)^k ≤ 2*(m:ℝ)^((p^2:ℕ):ℝ)⁻¹ →
      2*(m:ℝ)^γ + 2*(((2*p-1)*(2^k)^(2*p-1) : ℕ) : ℝ) < (m:ℝ)^α := by
  let h := 2*p-1
  let s := p^2
  let C := (h:ℝ)*2^h
  have h' : (h:ℝ) = 2*p-1 := by
    dsimp [h]; rw [Nat.cast_sub (by omega : 1 ≤ 2*p)]; push_cast; ring
  have hp' : 0 < (p:ℝ) := by exact_mod_cast hp
  have hβ : ((s:ℝ)⁻¹ * h) ≤ γ := by
    have h : ((2*p-1:ℝ)/(p:ℝ)^2) ≤ (3*p-1)/(p:ℝ)^2 := by
      gcongr; linarith
    rw [h']
    simp only [s,Nat.cast_pow]
    linarith only [h, hg, show 0 ≤ (1:ℝ)/2 by norm_num,
      show ((p:ℝ)^2)⁻¹ * (2*p-1) = (2*p-1)/(p:ℝ)^2 by ring]
  have ht : Tendsto (fun m : ℕ => (m : ℝ)^(α-γ)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hag)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_gt_atTop (2+2*C), eventually_ge_atTop (1:ℕ)] with m hm hm1
  intro k hk
  have h1 : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hmpos : (0:ℝ) < m := zero_lt_one.trans_le h1
  have haz : ((h*(2^k)^h : ℕ):ℝ) ≤ C*(m:ℝ)^γ := by
    push_cast
    have hz : ((m:ℝ)^((s:ℝ)⁻¹))^h = (m:ℝ)^((s:ℝ)⁻¹*h) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]
    calc
      _ ≤ (h:ℝ)*(2*(m:ℝ)^((s:ℝ)⁻¹))^h := by gcongr
      _ = C*(m:ℝ)^((s:ℝ)⁻¹*h) := by rw [mul_pow, hz]; dsimp [C]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 hβ)
        dsimp [C]; positivity
  calc
    _ ≤ (2+2*C)*(m:ℝ)^γ := by change 2*(m:ℝ)^γ + 2*((h*(2^k)^h : ℕ):ℝ) ≤ _; linarith
    _ < (m:ℝ)^(α-γ)*(m:ℝ)^γ := mul_lt_mul_of_pos_right hm (Real.rpow_pos_of_pos hmpos _)
    _ = _ := by rw [← Real.rpow_add hmpos, sub_add_cancel]

/-- Number of width-`f` recursive calls in the batched stage estimate with
`c` calls per address dimension in one local layout conversion. This integer
counts the unnormalized total over the independent rows and labels. -/
noncomputable def batchCalls (p k m c : ℕ) [Fact p.Prime] : ℕ :=
  let q := 2^k
  let D := Fintype.card (GramIndex (2*p-1) (Word p q))
  let N := Fintype.card (Label p q)
  let r := (hammingLabelMatrix p q).rank
  let inc := labelIncidence p k (Fact.out : p.Prime).pos
  (4*SwapRepair.order m)*(c*independentRows m*D*(1+inc)*(N+m*r)) +
    4*m*correctedRows m*N

/-- A characteristic and a dyadic label alphabet for which the main batch
cost and the occupied reserve fields simultaneously satisfy the recursion
inequalities. The characteristic depends only on the exponent, and the choice
of `k` works for every input at the chosen `m`. -/
theorem exists_contracted_batch {α γ : ℝ} (hγ : 1/2 < γ) (ha : γ < α) (c : ℕ) :
    ∃ p : ℕ, ∃ hp : Fact p.Prime, 2 < p ∧ ∀ᶠ m : ℕ in atTop, ∃ k : ℕ,
      let q := 2^k
      let reserve := (2*p-1) * q^(2*p-1)
      ((@batchCalls p k m c hp : ℕ) : ℝ) ≤ (independentRows m : ℝ) *
        Fintype.card (Label p q) * (m : ℝ)^γ ∧
      2*(m:ℝ)^γ + 2*reserve < (m:ℝ)^α := by
  obtain ⟨p, hp, hodd, hg⟩ := exists_interchange_characteristic hγ
  have : Fact p.Prime := ⟨hp⟩
  let B : ℝ := max 80 c
  refine ⟨p, inferInstance, hodd, ?_⟩
  filter_upwards [eventually_hamming_batch_budget p γ B hg, reserve_contraction hp.pos ha hg,
    eventually_ge_atTop (2:ℕ)] with m hmain hspace hm
  obtain ⟨k, _, hupp, hb⟩ := hmain
  refine ⟨k, ?_, hspace k (by simpa using hupp)⟩
  have hst : ((4*SwapRepair.order m : ℕ) : ℝ) ≤ B*Real.sqrt (m*(1+Real.log m)) :=
    (order_time m hm).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (Real.sqrt_nonneg _))
  have he := hb (4*SwapRepair.order m) (independentRows m) (correctedRows m)
    (independentRows_pos m) hst (correctedRows_le m)
  dsimp only [batchCalls]
  push_cast at he ⊢
  refine le_trans ?_ he
  gcongr
  exact le_max_right ..

end Interchange

end NearSquareRoot
end Computability
end OAI
