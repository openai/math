import OAI.LinearAlgebra.FiniteFourier.WorkingLengths
import OAI.LinearAlgebra.FiniteFourier.WorkingCapacity

/-! # A common extension for the Fourier transforms within one group of axes -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Finset Filter

section

variable (K : Type*) [Field K] {ι : Type*} [Fintype ι]

/-- The long and short working lengths for a group of axes. -/
structure WorkingGroup (a : ι → ℕ) (t : ℕ) where
  axes : ∀ i, WorkingFactors K (a i) t
  shortExponent : ℕ → ℕ
  short_lower : ∀ i, ∀ d ∈ (axes i).factors, 2 * d ≤ fourierRadix K ^ shortExponent d
  short_upper : ∀ i, ∀ d ∈ (axes i).factors, fourierRadix K ^ shortExponent d < 6 * d
  short_min : ∀ i, ∀ d ∈ (axes i).factors, ∀ j < shortExponent d, fourierRadix K ^ j < 2 * d

namespace WorkingGroup

variable {K} {a : ι → ℕ} {t : ℕ} (w : WorkingGroup K a t)

def length (i : ι) : ℕ := ∏ d ∈ (w.axes i).factors, d

def shortFactors : Finset ℕ := univ.biUnion (fun i ↦ (w.axes i).factors)

noncomputable def order : ℕ :=
  workingOrder univ w.length w.shortFactors (fun d ↦ fourierRadix K ^ w.shortExponent d)

theorem length_dvd_order (i : ι) : w.length i ∣ w.order :=
  (Finset.dvd_lcm (mem_univ i)).trans (Nat.dvd_lcm_left ..)

theorem short_dvd_order {i : ι} {d : ℕ} (hd : d ∈ (w.axes i).factors) :
    fourierRadix K ^ w.shortExponent d ∣ w.order :=
  (Finset.dvd_lcm (show d ∈ w.shortFactors from mem_biUnion.mpr ⟨i, mem_univ _, hd⟩)).trans
    (Nat.dvd_lcm_right ..)

theorem order_cast_ne_zero : (w.order : K) ≠ 0 := by
  apply workingOrder_cast_ne_zero
  · intro i _
    simpa [length] using Finset.prod_ne_zero_iff.mpr (w.axes i).cast_ne_zero
  · intro d _
    exact_mod_cast (show ((fourierRadix K : K) ^ w.shortExponent d) ≠ 0 from
      pow_ne_zero _ (fourierRadix_cast_ne_zero K))

theorem extension_degree_le : Module.finrank K (CyclotomicField w.order K) ≤ w.order := by
  let : NeZero (w.order : K) := ⟨w.order_cast_ne_zero⟩
  let : NeZero w.order := NeZero.of_neZero_natCast K
  exact working_cyclotomic_finrank_le K

/-- A single primitive root supplies all the long and short transforms of the group. -/
theorem exists_roots : ∃ ζ : CyclotomicField w.order K, IsPrimitiveRoot ζ w.order ∧
    (∀ i, IsPrimitiveRoot (ζ ^ (w.order / w.length i)) (w.length i)) ∧
    ∀ i, ∀ d ∈ (w.axes i).factors, IsPrimitiveRoot
      (ζ ^ (w.order / fourierRadix K ^ w.shortExponent d)) (fourierRadix K ^ w.shortExponent d) := by
  let : NeZero (w.order : K) := ⟨w.order_cast_ne_zero⟩
  let : NeZero w.order := NeZero.of_neZero_natCast K
  exact ⟨_, IsCyclotomicExtension.zeta_spec w.order K _, fun i ↦
    working_cyclotomic_root K (w.length_dvd_order i), fun _ _ hd ↦
    working_cyclotomic_root K (w.short_dvd_order hd)⟩

theorem order_le (ht : 0 < t) (ha : ∀ i, 2 ≤ a i) : w.order ≤ 18 * t ^ 2 * (∏ i, a i) ^ 4 := by
  apply workingOrder_le (j := w.shortExponent) ht (fourierRadix_prime K).pos
    (fun i _ ↦ ha i) (fun i _ ↦ (w.axes i).upper)
  · intro d hd
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp hd
    exact (w.axes i).factor_le _ hi
  · intros
    rfl
  · intro d hd
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp hd
    exact w.short_upper i _ hi

end WorkingGroup

/-- For sufficiently large total volume `N`, every axis group with `B¹² ≤ N` has
admissible long and short working lengths. Their common cyclotomic field has
degree at most `M`, and `M ≤ 18 t² B⁴ ≤ N/B`. The threshold is uniform in
the field and the axes. -/
theorem eventually_exists_workingGroup :
    ∀ᶠ N : ℕ in atTop, ∀ (K : Type*) [Field K] (ι : Type*) [Fintype ι] (a : ι → ℕ),
      (∀ i, 2 ≤ a i) → (∏ i, a i) ^ 12 ≤ N →
      ∃ w : WorkingGroup K a (Nat.clog 2 N),
        Module.finrank K (CyclotomicField w.order K) ≤ w.order ∧
        w.order ≤ 18 * (Nat.clog 2 N) ^ 2 * (∏ i, a i) ^ 4 ∧
        18 * (Nat.clog 2 N) ^ 2 * (∏ i, a i) ^ 4 ≤ N / (∏ i, a i) := by
  classical
  filter_upwards [eventually_exists_workingFactors, eventually_workingCapacity_le,
    eventually_gt_atTop (1 : ℕ)] with N hN hcap hNpos K _ ι _ a ha hvol
  let B := ∏ i, a i
  have hB : 0 < B := Finset.prod_pos (fun i _ ↦ by have := ha i; omega)
  have hau (i : ι) : a i ≤ N :=
    ((Finset.single_le_prod (fun j _ ↦ (ha j).trans' (by decide)) (mem_univ i)).trans
      (Nat.le_pow (by decide : 0 < 12))).trans hvol
  let axis (i : ι) := Classical.choice (hN K (a i) (ha i) (hau i))
  let j (d : ℕ) := if h : 2 ≤ d then Nat.find (exists_short_radix_order K h) else 0
  have hj (d : ℕ) (hd : 2 ≤ d) := Nat.find_spec (exists_short_radix_order K hd)
  let w : WorkingGroup K a (Nat.clog 2 N) :=
    { axes := axis
      shortExponent := j
      short_lower i d hd := by simpa [j, (axis i).factor_ge d hd] using (hj d ((axis i).factor_ge d hd)).1
      short_upper i d hd := by simpa [j, (axis i).factor_ge d hd] using (hj d ((axis i).factor_ge d hd)).2.1
      short_min i d hd := by simpa [j, (axis i).factor_ge d hd] using (hj d ((axis i).factor_ge d hd)).2.2 }
  exact ⟨w, w.extension_degree_le, w.order_le (Nat.clog_pos (by decide) hNpos) ha,
    hcap B hB hvol⟩

end

end FiniteFourier
end LinearAlgebra
end OAI
