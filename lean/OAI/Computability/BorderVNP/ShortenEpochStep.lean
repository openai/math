import OAI.Computability.BorderVNP.ShortenEpochMatching
import OAI.Computability.BorderVNP.ShortenEpochConcentration
import OAI.Computability.BorderVNP.ShortenEpochLocality

/-!
# Quantitative estimates for one combining step

These are the two estimates in (6.3). Their inputs separate the profile's
geometric saving, the finite-motion mean estimate, and the deviations bounded
in (6.2). In particular the error from integer pooling is divided by the
number of packs. The concentration estimate allows new incidences to be
duplicated among boundedly many neighboring tiles.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open Finset

variable {T B J : Type*} [Fintype T] [Fintype B] [Fintype J] [Nonempty J]

/-- The length estimate in (6.3), retaining the precise pooling cost and the
weighted variation constant for the actual bin arrays. -/
theorem normalized_length_saving (A : J → Equiv.Perm (T × B)) (length : T × B → ℝ)
    {h : ℝ} (hlen : ∀ b, 0 ≤ length b ∧ length b ≤ h) (hh : 0 ≤ h)
    (hpres : ∀ j b, length (A j b) = length b)
    (counts : T × B → ℕ) (mean : T × B → ℝ) {K ν W out err : ℝ} (hK : 0 < K) (hν : 0 ≤ ν)
    {m : ℕ} (hm : 0 < m)
    (hmean : W / 2 ≤ matchedLength A length mean)
    (hdev : Real.sqrt (Fintype.card T) *
        Real.sqrt (binEnergy (fun b => counts b / K - mean b)) ≤ err)
    (hsave : out / K ≤ W - ν * ((∑ b, length b * pooledBits m (fun j => counts (A j b))) / K)) :
    out / K ≤ (1 - ν / 2) * W +
        ν * (Fintype.card J * (h * (Real.sqrt (Fintype.card B) * err))) +
        ν * ((∑ b, length b * (Fintype.card J * m : ℕ)) / K) := by
  let s : T × B → ℝ := fun b => counts b / K
  let error := fun b => s b - mean b
  let pooled := ∑ b, length b * pooledBits m (fun j => counts (A j b))
  let loss := ∑ b, length b * (Fintype.card J * m : ℕ)
  have herr : (∑ b, |error b|) ≤ Real.sqrt (Fintype.card B) * err :=
    (tile_l1_le error).trans (mul_le_mul_of_nonneg_left hdev (Real.sqrt_nonneg _))
  have htotal : (∑ b, length b * |error b|) ≤ h * (Real.sqrt (Fintype.card B) * err) := by
    calc
      _ ≤ ∑ b, h * |error b| := sum_le_sum fun b _ =>
        mul_le_mul_of_nonneg_right (hlen b).2 (abs_nonneg _)
      _ = h * ∑ b, |error b| := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left herr hh
  have hlip := matchedLength_lipschitz A length s mean (fun b => (hlen b).1) hpres
  have hdiff := (abs_le.mp hlip).1
  have hweight := mul_le_mul_of_nonneg_left htotal
    (Nat.cast_nonneg (α := ℝ) (Fintype.card J))
  have hmatch : W / 2 - Fintype.card J * (h * (Real.sqrt (Fintype.card B) * err)) ≤
      matchedLength A length s := by
    change _ ≤ Fintype.card J * ∑ b, length b * |s b - mean b| at hlip
    dsimp [error] at hweight
    linarith
  have hpool := pooledLength_loss_le A length counts hm (fun b => (hlen b).1)
  change matchedLength A length (fun b => counts b) - pooled ≤ loss at hpool
  have hscaled := div_le_div_of_nonneg_right hpool hK.le
  rw [sub_div, ← matchedLength_div A length (fun b => (counts b : ℝ)) hK.le] at hscaled
  have hcombined : W / 2 - Fintype.card J * (h * (Real.sqrt (Fintype.card B) * err)) -
      loss / K ≤ pooled / K := by
    change matchedLength A length s - pooled / K ≤ loss / K at hscaled
    linarith
  have hweighted := mul_le_mul_of_nonneg_left hcombined hν
  change out / K ≤ W - ν * (pooled / K) at hsave
  change out / K ≤ (1 - ν / 2) * W + _ + ν * (loss / K)
  linarith

private theorem sqrt_binEnergy_triangle {α : Type*} [Fintype α] (x y : α → ℝ) :
    Real.sqrt (binEnergy (fun a => x a + y a)) ≤
      Real.sqrt (binEnergy x) + Real.sqrt (binEnergy y) := by
  have hx : 0 ≤ binEnergy x := sum_nonneg fun a _ => sq_nonneg (x a)
  have hy : 0 ≤ binEnergy y := sum_nonneg fun a _ => sq_nonneg (y a)
  have hid : binEnergy (fun a => x a + y a) = binEnergy x + binEnergy y + 2 * ∑ a, x a * y a := by
    simp only [binEnergy, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro a _
    ring
  have hxy := Real.sum_mul_le_sqrt_mul_sqrt univ x y
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [hid]
  change _ ≤ Real.sqrt (binEnergy x) * Real.sqrt (binEnergy y) at hxy
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]

/-- The concentration estimate in (6.3) for profile replacements with
bounded neighboring source and output tiles. -/
theorem normalized_concentration [DecidableEq (T × B)]
    (near : T → Finset (T × B)) (s g : T × B → ℝ) (new : T → ℝ)
    (fanIn fanOut : ℕ) {W err : ℝ} (hnew : ∀ t, 0 ≤ new t)
    (hload : ∀ t, new t ≤ ∑ b ∈ near t, s b)
    (hIn : ∀ t, (near t).card ≤ fanIn)
    (hOut : ∀ b, (univ.filter fun t => b ∈ near t).card ≤ fanOut)
    (hmean : Real.sqrt (Fintype.card T) * Real.sqrt (binEnergy g) ≤ W)
    (hdev : Real.sqrt (Fintype.card T) * Real.sqrt (binEnergy (fun b => s b - g b)) ≤ err) :
    Real.sqrt (Fintype.card T) * Real.sqrt (binEnergy new) ≤
      Real.sqrt ((fanIn : ℝ) * fanOut) * (W + err) := by
  have hloc := sum_sq_locality near s new fanIn fanOut hnew hload hIn hOut
  change binEnergy new ≤ _ * binEnergy s at hloc
  have hs := Real.sqrt_le_sqrt hloc
  rw [Real.sqrt_mul (by positivity)] at hs
  have htri := sqrt_binEnergy_triangle g (fun b => s b - g b)
  simp only [add_sub_cancel] at htri
  calc
    _ ≤ Real.sqrt (Fintype.card T) * (Real.sqrt ((fanIn : ℝ) * fanOut) * Real.sqrt (binEnergy s)) :=
      mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt ((fanIn : ℝ) * fanOut) * (Real.sqrt (Fintype.card T) *
        (Real.sqrt (binEnergy g) + Real.sqrt (binEnergy (fun b => s b - g b)))) := by
      rw [mul_left_comm]
      gcongr
    _ ≤ _ := by rw [mul_add]; exact mul_le_mul_of_nonneg_left (add_le_add hmean hdev) (Real.sqrt_nonneg _)

end Epoch

end BorderVNP
end Computability
end OAI
