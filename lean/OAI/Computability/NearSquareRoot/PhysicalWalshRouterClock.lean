import OAI.Computability.NearSquareRoot.PhysicalWalshSwapStage
import OAI.Computability.NearSquareRoot.PhysicalWalshElementaryPrefix
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeEnvelope
import OAI.Computability.NearSquareRoot.Asymptotic

/-! # Paying for Walsh address routing at a recursive node

The rectangular swap and the guarded XOR share a word-volume factor. The
logarithmic factor from their elementary scans depends on the compact
descriptor, whose size is linear in the precision on an occupied node.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.RouterClock

open PhysicalWalsh ElementarySchedule

noncomputable def logWidth (n : ℕ) : ℝ := 1 + Real.log (2+n)

theorem one_le_logWidth (n : ℕ) : 1 ≤ logWidth n := by
  have h := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n] : 1 ≤ 2+(n:ℝ))
  unfold logWidth
  linarith

/-- Charge the logarithm of a work width bounded by a fixed multiple of the
input precision to one logarithm of the input precision. -/
theorem logWidth_linear_real {R : ℝ} (hR : 0 ≤ R) {w k : ℕ} (bound : (w:ℝ) ≤ R*(k+1)) :
    logWidth w ≤ (R+3 : ℝ)*logWidth k := by
  have hk := Nat.cast_nonneg (α:=ℝ) k
  have cmp : 2+(w:ℝ) ≤ ((R:ℝ)+2)*(2+k) := by nlinarith
  have logb := Real.log_le_log (by positivity : 0 < 2+(w:ℝ)) cmp
  rw [Real.log_mul (by positivity) (by positivity)] at logb
  have cheap := Real.log_le_sub_one_of_pos (show 0 < (R:ℝ)+2 by positivity)
  have hpos := one_le_logWidth k
  unfold logWidth at hpos ⊢
  nlinarith [mul_nonneg hR (show 0 ≤ Real.log (2+(k:ℝ)) by linarith)]

theorem logWidth_linear (R : ℕ) {w k : ℕ} (bound : w ≤ R*(k+1)) :
    logWidth w ≤ (R+3 : ℝ)*logWidth k :=
  logWidth_linear_real (Nat.cast_nonneg R) (by exact_mod_cast bound)

theorem scaleLog {A : ℕ} (arity : 2 ≤ A) {s : Shape} (admit : withinWidth A s) :
    logWidth (Header.scale A s) ≤ 37 * logWidth s.w := by
  have h := Header.scale_le_of_count (k:=s.w+1) arity s admit
  convert logWidth_linear 34 (w:=Header.scale A s) (k:=s.w) (by omega) using 1
  norm_num

def rawVolume (A : ℕ) (s : Shape) := (count A s+1)*(s.w+1)

noncomputable def unit (A : ℕ) (ρ : ℝ) (s : Shape) :=
  (rawVolume A s : ℝ)*logWidth (Header.scale A s)*(1+(slotWidth A s:ℝ)^ρ)

theorem rawVolume_pos (A : ℕ) (s : Shape) : 0 < rawVolume A s :=
  Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)

theorem rawVolume_le (A : ℕ) (s : Shape) : (rawVolume A s:ℝ) ≤ 2*bitVolume A s := by
  have hc : 0 < count A s := Nat.mul_pos s.pref_pos (Nat.mul_pos (Nat.two_pow_pos _) s.suff_pos)
  have hd : ((count A s : ℝ)+1) ≤ 2*(count A s:ℝ) := by
    have h : 1 ≤ (count A s:ℝ) := by exact_mod_cast hc
    linarith
  simpa [rawVolume,bitVolume,mul_assoc] using mul_le_mul_of_nonneg_right hd (by positivity : 0 ≤ (s.w:ℝ)+1)

theorem one_le_unit (A : ℕ) (ρ : ℝ) (s : Shape) : 1 ≤ unit A ρ s := by
  have v : (1:ℝ) ≤ rawVolume A s := by exact_mod_cast rawVolume_pos A s
  have p : (0:ℝ) ≤ (slotWidth A s:ℝ)^ρ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le v (one_le_logWidth _)) (by linarith)

/-- A node-level estimate for any router whose extra scans are at most a
constant multiple of the measured word volume, log factor and moving width. -/
theorem unit_local {A : ℕ} (arity : 2 ≤ A) {ρ C : ℝ} (hr : 0 ≤ ρ) (hC : 0 ≤ C)
    {s : Shape} (admit : withinWidth A s) {t : ℝ} (ht : t ≤ C*unit A ρ s) :
    t ≤ localTime A ρ (74*C) (logWidth s.w) 0 s.level (bitVolume A s) := by
  have exp : (slotWidth A s:ℝ) ≤ (2:ℝ) * (A:ℝ)^s.level := by
    exact_mod_cast Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega : 0 < A) (Nat.sub_le s.level 1))
  have rate := Real.rpow_le_rpow (Nat.cast_nonneg _) exp hr
  have base := mul_le_mul (rawVolume_le A s) (scaleLog arity admit)
    (zero_le_one.trans (one_le_logWidth _)) (by positivity [bitVolume_nonneg A s])
  have full := mul_le_mul base (add_le_add_right rate 1) (by positivity)
    (mul_nonneg (by positivity [bitVolume_nonneg A s]) (by linarith [one_le_logWidth s.w]))
  calc
    _ ≤ C * unit A ρ s := ht
    _ ≤ C*((2*bitVolume A s)*(37*logWidth s.w)*(1+((2:ℝ)*(A:ℝ)^s.level)^ρ)) :=
      mul_le_mul_of_nonneg_left full hC
    _ = _ := by unfold localTime; ring

/-- Rounding up the physical scan clock only changes its uniform coefficient. -/
theorem ceil_local {A : ℕ} (arity : 2 ≤ A) {ρ : ℝ} (hr : 0 ≤ ρ)
    {s : Shape} (admit : withinWidth A s) :
    (⌈unit A ρ s⌉₊:ℝ) ≤ localTime A ρ 148 (logWidth s.w) 0 s.level (bitVolume A s) := by
  have pos := one_le_unit A ρ s
  have small := Nat.ceil_lt_add_one (by linarith : 0 ≤ unit A ρ s)
  convert unit_local arity hr (C:=2) (t:=(⌈unit A ρ s⌉₊:ℝ)) (by norm_num) admit (by linarith) using 1
  norm_num

theorem clog_logWidth (n : ℕ) :
    (Nat.clog 2 (n+1):ℝ) ≤ (1+(Real.log 2)⁻¹)*logWidth n := by
  have hs : logScale (n+1) ≤ logWidth n := by
    unfold logWidth logScale
    push_cast
    have h := Real.log_le_log (show 0 < (n:ℝ)+1 by positivity) (show (n:ℝ)+1 ≤ 2+n by linarith)
    linarith
  have hmax : (Nat.clog 2 (n+1):ℝ) ≤ (max 1 (Nat.clog 2 (n+1)) : ℕ) :=
    Nat.cast_le.mpr (le_max_right ..)
  exact (hmax.trans (clog_le_logScale (Nat.succ_pos n))).trans
    (mul_le_mul_of_nonneg_left hs (by positivity))

/-- A truncated elementary prefix costs a single logarithmic multiplier,
uniformly for the degree selected by the rectangular program. -/
theorem prefix_bound (D A : ℕ) (ρ : ℝ) (s : Shape) :
    (ElementarySweep.prefixExtra A (SlotSwap.reserve D A) s : ℝ) ≤
      (D*(1+(Real.log 2)⁻¹)+1)*unit A ρ s := by
  let q := Header.scale A s
  have bound : (SlotSwap.reserve D A s : ℝ) ≤ (D:ℝ) * (Nat.clog 2 (q+1) : ℝ) := by
    exact_mod_cast (min_le_right (slotWidth A s) (Controlled.payloadBits D q))
  have hcut := bound.trans (mul_le_mul_of_nonneg_left (clog_logWidth q) (Nat.cast_nonneg _))
  have one := one_le_logWidth q
  have h : (SlotSwap.reserve D A s:ℝ)+1 ≤ (D*(1+(Real.log 2)⁻¹)+1)*logWidth q := by
    linarith only [hcut,one]
  have p : 1 ≤ 1+(slotWidth A s:ℝ)^ρ := by linarith [Real.rpow_nonneg (Nat.cast_nonneg (slotWidth A s)) ρ]
  change (((SlotSwap.reserve D A s+1)*rawVolume A s:ℕ):ℝ) ≤ _
  push_cast
  calc
    _ ≤ ((D*(1+(Real.log 2)⁻¹)+1)*logWidth q)*(rawVolume A s:ℝ) :=
      mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)
    _ ≤ (((D*(1+(Real.log 2)⁻¹)+1)*logWidth q)*(rawVolume A s:ℝ))*(1+(slotWidth A s:ℝ)^ρ) :=
      le_mul_of_one_le_right (mul_nonneg (mul_nonneg (by positivity) (zero_le_one.trans one)) (Nat.cast_nonneg _)) p
    _ = _ := by unfold unit; dsimp only [q]; ring

/-- The physical whole-field exchange is charged at the rate of the moving
window. The added unit covers rounding its scan count to a natural. -/
theorem wide_bound {A : ℕ} (positive : 0 < A) {ρ : ℝ} (hr : 0 ≤ ρ) (s : Shape) :
    (SlotSwap.wideExtra ρ A s : ℝ) ≤ ((2:ℝ)^ρ+1)*unit A ρ s := by
  let L := slotWidth A s
  have pos : 0 < L := Nat.mul_pos (by decide) (pow_pos positive _)
  have le : ((L+1 : ℕ):ℝ) ≤ 2*(L:ℝ) := by exact_mod_cast (show L+1 ≤ 2*L by omega)
  have pow := Real.rpow_le_rpow (by positivity) le hr
  rw [Real.mul_rpow (by norm_num) (by positivity)] at pow
  have one : 1 ≤ logWidth (Header.scale A s) := one_le_logWidth _
  have base : (rawVolume A s:ℝ)*(L:ℝ)^ρ ≤ unit A ρ s := by
    unfold unit
    exact mul_le_mul (le_mul_of_one_le_right (Nat.cast_nonneg _) one) (by dsimp [L]; linarith)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans one))
  have b : (rawVolume A s:ℝ)*((L+1:ℕ):ℝ)^ρ ≤ (2:ℝ)^ρ*unit A ρ s := calc
    _ ≤ (rawVolume A s:ℝ)*((2:ℝ)^ρ*(L:ℝ)^ρ) := mul_le_mul_of_nonneg_left pow (Nat.cast_nonneg _)
    _ = (2:ℝ)^ρ*((rawVolume A s:ℝ)*(L:ℝ)^ρ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left base (by positivity)
  have ceil := Nat.ceil_lt_add_one (show 0 ≤ (rawVolume A s:ℝ)*((L+1:ℕ):ℝ)^ρ by positivity)
  change (⌈(rawVolume A s:ℝ)*((L+1:ℕ):ℝ)^ρ⌉₊:ℝ) ≤ _
  linarith only [ceil,b,one_le_unit A ρ s]

/-- A complete router clock combines the truncated prefix, rectangular
interchanges and a central operation bounded on the same physical volume. -/
theorem combined_clock (D : ℕ) {A : ℕ} (arity : 2 ≤ A) {ρ : ℝ} (hr : 0 ≤ ρ)
    {front : Shape → ℕ} {B : ℝ} (hB : 0 ≤ B)
    (central : ∀ s, withinWidth A s → (front s : ℝ) ≤ B*unit A ρ s) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ s, withinWidth A s →
      ((ElementarySweep.prefixExtra A (SlotSwap.reserve D A) s + SlotSwap.wideExtra ρ A s + front s : ℕ):ℝ) ≤
        localTime A ρ c (logWidth s.w) 0 s.level (bitVolume A s) := by
  let C : ℝ := (D*(1+(Real.log 2)⁻¹)+1) + ((2:ℝ)^ρ+1) + B
  have cp : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨74*C,by positivity,fun s h => unit_local arity hr cp h ?_⟩
  have a := prefix_bound D A ρ s
  have b := wide_bound (by omega : 0 < A) hr s
  have f := central s h
  dsimp [C]
  push_cast
  linarith only [a,b,f]

end PhysicalWalshNode.RouterClock

end NearSquareRoot
end Computability
end OAI
