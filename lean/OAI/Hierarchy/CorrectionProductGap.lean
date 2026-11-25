import OAI.Hierarchy.CorrectionProducts
import OAI.Hierarchy.GridSum

namespace OAI
/-! # Ordinary error of an independent product at a common frame

Each nonempty subset of erroneous rows saves at least one copy of the gap.
The frame's binary diagonal pays for the choice of the subset.
-/

noncomputable section
namespace Hierarchy.CorrectionProducts
open LinearAlgebra.SpectralBooks SiteTensor
open scoped Classical BigOperators NNReal
variable {F M : Type*} [Field F] [MetricSpace M]
  {I J : Type} [Fintype I] [Fintype J] [Nontrivial J] {d : ℕ}

def rows (g : Fin d → (I → Bool) → F) (x : Fin d × I → Bool) : F :=
  ∏ i, g i (fun j => x (i,j))

omit [Fintype I] in
private theorem rows_nonzero {g : Fin d → (I → Bool) → F} (h : rows g ≠ 0) (i : Fin d) :
    g i ≠ 0 := by
  intro z
  apply h
  funext x
  exact Finset.prod_eq_zero (Finset.mem_univ i) (congrFun z _)

/-- Logarithmic price adds across physically disjoint rows whose ports map
to the same labelled sites. Each row may have a different coefficient table. -/
theorem rows_price (Q : SpectralPlacementPrices F M) (y : J ↪ M) (σ : I → J)
    (g : Fin d → (I → Bool) → F) (nz : rows g ≠ 0) :
    Q.price (raw (rows g)) (y ∘ (σ ∘ Prod.snd)) =
      ∑ i, Q.price (raw (g i)) (y ∘ σ) := by
  obtain ⟨φ,_,price⟩ := Q.normalized_group y
  let c := Q.price (Raw.diagonal J F (Fin 2)) y
  rw [price (σ ∘ Prod.snd) _ nz]
  change c*Real.logb 2 (value φ (σ ∘ Prod.snd) (rows g)) = _
  rw [show value φ (σ ∘ Prod.snd) (rows g) = ∏ i, value φ σ (g i) from value_product φ σ g,
    NNReal.coe_prod, Real.logb_prod, Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro i _
    exact (price σ (raw (g i)) (rows_nonzero nz i)).symm
  · intro i _
    exact_mod_cast (value_pos φ σ (rows_nonzero nz i)).ne'

private def changed (a b : Fin d → (I → Bool) → F) (s : Finset (Fin d)) (i : Fin d) :=
  if i ∈ s then a i - b i else b i

omit [Fintype I] in
theorem rows_difference (a b : Fin d → (I → Bool) → F) :
    rows a - rows b =
      ∑ s : {s : Finset (Fin d) // s ≠ ∅}, rows (changed a b s.val) := by
  funext x
  rw [Pi.sub_apply,Finset.sum_apply x Finset.univ (fun s : {s : Finset (Fin d) // s ≠ ∅} =>
    rows (changed a b s.val))]
  unfold rows
  rw [GridSum.expand]
  apply Finset.sum_congr (by ext s; simp)
  intro s _
  symm
  rw [← s.val.prod_mul_prod_compl (fun i => changed a b s.val i (fun j => x (i,j)))]
  congr 1
  · exact Finset.prod_congr rfl fun i hi => by simp [changed,hi]
  · apply Finset.prod_congr (by ext i; simp)
    intro i hi
    have hn : i ∉ s.val := by simpa using hi
    simp [changed,hn]

theorem rows_error_price (Q : SpectralPlacementPrices F M) (y : J ↪ M) (σ : I → J)
    (a b : Fin d → (I → Bool) → F) {B D c : ℝ} (hD : 0 ≤ D)
    (scale : Q.price (Raw.diagonal J F (Fin 2)) y ≤ c)
    (base : ∀ i, Q.price (raw (b i)) (y ∘ σ) ≤ B)
    (err : ∀ i, a i-b i ≠ 0 → Q.price (raw (a i-b i)) (y ∘ σ) ≤ B-D)
    (nz : rows a-rows b ≠ 0) :
    Q.price (raw (rows a-rows b)) (y ∘ (σ ∘ Prod.snd)) ≤ d*B-D+c*d := by
  let terms (s : {s : Finset (Fin d) // s ≠ ∅}) := rows (changed a b s.val)
  have expand : rows a-rows b = ∑ s, terms s := rows_difference a b
  rw [expand] at nz ⊢
  obtain ⟨s,hs,price⟩ := GridSum.price_sum Q y (σ ∘ Prod.snd) terms nz
  have rowBound (i : Fin d) : Q.price (raw (changed a b s.val i)) (y ∘ σ) ≤
      B - (if i ∈ s.val then D else 0) := by
    by_cases h : i ∈ s.val
    · have hit := rows_nonzero hs i
      simpa only [changed,ite_eq_left h] using err i (by simpa [changed,h] using hit)
    · simpa only [changed,ite_eq_right h,sub_zero] using base i
  have paid := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => rowBound i)
  have saved : (∑ i : Fin d, if i ∈ s.val then D else 0) = (s.val.card:ℝ)*D := by
    simp [Finset.sum_ite_mem, nsmul_eq_mul]
  rw [Finset.sum_sub_distrib,saved] at paid
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at paid
  have count : Fintype.card {s : Finset (Fin d) // s ≠ ∅} ≤ 2^d :=
    (Fintype.card_subtype_le _).trans (by simp)
  have pos : 0 < Fintype.card {s : Finset (Fin d) // s ≠ ∅} := Fintype.card_pos_iff.mpr ⟨s⟩
  have lg := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by exact_mod_cast pos)
    (show (Fintype.card {s : Finset (Fin d) // s ≠ ∅} : ℝ) ≤ (2:ℝ)^d by exact_mod_cast count)
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),mul_one] at lg
  have fee := (mul_le_mul_of_nonneg_left lg (Q.diagonal_pos y).le).trans
    (mul_le_mul_of_nonneg_right scale (Nat.cast_nonneg d))
  have one : 1 ≤ (s.val.card : ℝ) := by
    exact_mod_cast (Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr s.property))
  change Q.price (raw (∑ s, terms s)) _ ≤ Q.price (raw (rows (changed a b s.val))) _ + _ at price
  rw [rows_price Q y σ _ hs] at price
  linarith [mul_le_mul_of_nonneg_right one hD]

end Hierarchy.CorrectionProducts

end
end OAI
