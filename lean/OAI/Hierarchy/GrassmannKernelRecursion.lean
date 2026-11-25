import OAI.Hierarchy.MatchedFiberKernel
import OAI.ThreeFlat.ExpanderTransfer
import Mathlib.Tactic

namespace OAI
/-! # Iterating the Grassmann paired-fiber kernel

A strict gap below the number of coordinates persists under iteration:
matching the two fiber partitions contributes an additive cost at each
stage. A slightly larger exponential rate absorbs that cost.
-/

noncomputable section
namespace Hierarchy.NonlinearExpanders

open Finset Matrix ThreeFlat.Expander
open scoped Classical

universe u v

theorem sparse_kernels_of_matched_partitions
    {m : ℕ} (hm : 2 ≤ m) {b : ℝ} (_hb : 0 ≤ b) (hbm : b < m)
    {J : Type*} [Fintype J] [Nonempty J]
    {I : Type v} (X : I → Type u) [∀ i, PseudoMetricSpace (X i)]
    (partitions : ∀ k : ℕ, ∃ e f : J → Fin ((2^k)^m) ≃ Fin (2^k) × Fin ((2^k)^(m-1)),
      ∀ i (x : Fin ((2^k)^m) → X i), variance x ≤ b*pairedEnergy e f x) :
    ∃ (K : ℕ) (α C : ℝ), 0 < K ∧ 0 < α ∧ α < m ∧ 0 ≤ C ∧
      ∀ n j : ℕ, ∃ G : Matrix (Fin ((2^n)^(m^j))) (Fin ((2^n)^(m^j))) ℝ,
        G ∈ rowStochastic ℝ _ ∧ (∀ a b, G a b = G b a) ∧
        (∀ a, (univ.filter fun b => G a b ≠ 0).card ≤ K^j*2^n) ∧
        ∀ i, Bound G (X i) (C*α^j) := by
  classical
  let β := max 1 b
  have βpos : 0 < β := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have βone : 1 ≤ β := le_max_left _ _
  have βm : β < m := max_lt (by exact_mod_cast (show 1 < m by omega)) hbm
  let α := (β + m)/2
  have βα : β < α := by dsimp [α]; linarith
  have αone : 1 ≤ α := βone.trans βα.le
  let ε := (α-β)/(2*β)
  have εpos : 0 < ε := div_pos (sub_pos.mpr βα) (by positivity)
  let w := 1+1/ε
  have wpos : 0 < w := by dsimp [w]; positivity
  have coeff : β*(1+ε) = (α+β)/2 := by dsimp [ε]; field_simp; ring
  have saving : 0 < α - β*(1+ε) := by rw [coeff]; linarith
  let C := max 1 (β*w/(α-β*(1+ε)))
  have Cone : 1 ≤ C := le_max_left _ _
  have Cpos : 0 ≤ C := zero_le_one.trans Cone
  have offset : β*w ≤ C*(α-β*(1+ε)) :=
    (div_le_iff₀ saving).mp (le_max_right _ _)
  let K := 3 * Fintype.card J
  have Kpos : 0 < K := Nat.mul_pos (by decide) Fintype.card_pos
  refine ⟨K,α,C,Kpos,by linarith,by dsimp [α]; linarith,Cpos,?_⟩
  intro n j
  induction j with
  | zero =>
    refine ⟨uniformKernel _,uniformKernel_row _,uniformKernel_symmetric,?_,?_⟩
    · intro a
      exact (card_filter_le _ _).trans (by rw [card_univ, Fintype.card_fin]; simp)
    · intro i x
      rw [energy_uniformKernel x, pow_zero α, mul_one]
      exact le_mul_of_one_le_left (avg_nonneg fun a => avg_nonneg fun b => sq_nonneg (dist (x a) (x b))) Cone
  | succ j ih =>
    obtain ⟨G, row, sym, supp, bound⟩ := ih
    let k := n * m^j
    obtain ⟨e,f,frame⟩ := partitions k
    let V := Fin ((2^n)^(m^j))
    let g : V ≃ Fin (2^k) := finCongr (pow_mul (2:ℕ) n (m^j)).symm
    let G' := reindexKernel g G
    have row' := reindexKernel_row g row
    have sym' := reindexKernel_symmetric g sym
    have supp' (a) : (univ.filter fun b => G' a b ≠ 0).card ≤ K^j*2^n := by
      change (univ.filter fun b => reindexKernel g G a b ≠ 0).card ≤ _
      rw [card_support_reindexKernel]; exact supp _
    let γ := C*α^j
    have hγ : 0 ≤ γ := mul_nonneg Cpos (pow_nonneg (by linarith) _)
    let v := (1+ε)*γ
    have hv : 0 ≤ v := mul_nonneg (by linarith) hγ
    let H := matchedKernel e f G' v w
    let g' : Fin ((2^k)^m) ≃ Fin ((2^n)^(m^(j+1))) :=
      finCongr (by dsimp [k]; rw [← pow_mul, pow_succ m, Nat.mul_assoc, pow_mul])
    refine ⟨reindexKernel g' H,reindexKernel_row g' (matchedKernel_row e f row' hv wpos),
      reindexKernel_symmetric g' (matchedKernel_symm e f sym' v w),?_,?_⟩
    · intro a
      rw [card_support_reindexKernel]
      apply (matchedKernel_sparse e f supp' v w _).trans
      have hs : 1 ≤ K^j * 2^n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
        (pow_ne_zero _ Kpos.ne') (pow_ne_zero _ (by decide)))
      calc
        _ ≤ Fintype.card J * (3*(K^j*2^n)) := Nat.mul_le_mul_left _ (by omega)
        _ = _ := by dsimp [K]; rw [pow_succ]; ring
    · intro i x
      have frame' (y : Fin ((2^k)^m) → X i) :
          variance y ≤ β * pairedEnergy e f y := (frame i y).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (avg_nonneg fun _ => avg_nonneg fun _ =>
          avg_nonneg fun _ => avg_nonneg fun _ => sq_nonneg _))
      have hbnd := (bound_matchedKernel e f hγ βpos.le εpos
        ((bound i).reindexKernel g) frame').reindexKernel g'
      apply (hbnd x).trans
      apply mul_le_mul_of_nonneg_right _
        (avg_nonneg fun a => sum_nonneg fun b _ => mul_nonneg
          ((mem_rowStochastic_iff_sum.mp (reindexKernel_row g' (matchedKernel_row e f row' hv wpos))).1 a b)
          (sq_nonneg _))
      have hpow : 1 ≤ α^j := one_le_pow₀ αone
      have o' : β*w ≤ (C*(α-β*(1+ε)))*α^j :=
        offset.trans (le_mul_of_one_le_right (mul_nonneg Cpos saving.le) hpow)
      change β*((1+ε)*(C*α^j)+w) ≤ C*α^(j+1)
      rw [pow_succ]
      linarith only [o']

end Hierarchy.NonlinearExpanders

end
end OAI
