import OAI.Computability.NearSquareRoot.PhysicalWalshPieceExecution

/-! # Absorbing finitely many exceptional Walsh widths in a uniform clock

A small outer width admits only finitely many selector counts and fixed-point
widths. The encoded sweep cost depends on these three integers. Its value on
all exceptional rows is consequently covered by one machine constant.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces

open Filter

private theorem bounded_cube (f : ℕ → ℕ → ℕ → ℕ) (x y z : ℕ) :
    ∃ M : ℕ, ∀ k ≤ x, ∀ s ≤ y, ∀ w ≤ z, f k s w ≤ M := by
  let last k s := (Finset.Iic z).sup (f k s)
  let middle k := (Finset.Iic y).sup (last k)
  refine ⟨(Finset.Iic x).sup middle,fun k hk s hs w hw => ?_⟩
  exact (Finset.le_sup (f := f k s) (Finset.mem_Iic.mpr hw)).trans
    ((Finset.le_sup (f := last k) (Finset.mem_Iic.mpr hs)).trans
      (Finset.le_sup (f := middle) (Finset.mem_Iic.mpr hk)))

theorem absorb_small_widths {I : Type*} (b : I → Root) (cost : ℕ → ℕ → ℕ → ℕ) (meter : ℕ → ℝ)
    (positive : ∀ k, 0 ≤ meter k) {g R E : ℝ} (hg : 0 ≤ g) (hR : 0 ≤ R)
    (sparse : ∀ i, ((b i).s:ℝ) ≤ g*(b i).k/Real.log (2+(b i).k))
    (width : ∀ i, ((b i).w:ℝ) ≤ R*((b i).k+1))
    (large : ∀ᶠ k : ℕ in atTop, ∀ i, (b i).k=k → (cost k (b i).s (b i).w:ℝ) ≤ E*meter k) :
    ∃ C : ℕ, ∀ i, cost (b i).k (b i).s (b i).w+1 ≤ C*(⌈meter (b i).k⌉₊+1) := by
  obtain ⟨K,suff⟩ := Filter.eventually_atTop.mp large
  obtain ⟨M,small⟩ := bounded_cube cost K ⌈g*K/Real.log 2⌉₊ ⌈R*((K:ℝ)+1)⌉₊
  let D := max (⌈E⌉₊+1) (M+1)
  refine ⟨D,fun i => ?_⟩
  by_cases hi : K ≤ (b i).k
  · have realBound := (suff _ hi i rfl).trans <| mul_le_mul (Nat.le_ceil E) (Nat.le_ceil (meter (b i).k))
        (positive _) (Nat.cast_nonneg _)
    have h : cost (b i).k (b i).s (b i).w ≤ ⌈E⌉₊*⌈meter (b i).k⌉₊ := by exact_mod_cast realBound
    have coeff : ⌈E⌉₊+1 ≤ D := le_max_left ..
    apply le_trans _ (Nat.mul_le_mul_right _ coeff)
    rw [Nat.succ_mul,Nat.mul_succ]; omega
  · have hk : (b i).k ≤ K := by omega
    have hr : ((b i).k:ℝ) ≤ K := by exact_mod_cast hk
    have hpos := Real.log_pos (by norm_num : (1:ℝ)<2)
    have hl : Real.log 2 ≤ Real.log (2+((b i).k:ℝ)) := Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) (b i).k])
    have hs := (((sparse i).trans (div_le_div_of_nonneg_left (mul_nonneg hg (Nat.cast_nonneg _)) hpos hl)).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr hg) hpos.le)).trans (Nat.le_ceil _)
    have hw := ((width i).trans (mul_le_mul_of_nonneg_left (add_le_add hr (le_refl (1:ℝ))) hR)).trans (Nat.le_ceil _)
    have low := small (b i).k hk (b i).s (by exact_mod_cast hs) (b i).w (by exact_mod_cast hw)
    exact (Nat.succ_le_succ low).trans ((le_max_right ..).trans (Nat.le_mul_of_pos_right D (Nat.succ_pos _)))

end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
