import OAI.LinearAlgebra.MatrixExponent.Upper.Character.Tag
import Mathlib.Analysis.MeanInequalities
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse.Model
import OAI.LinearAlgebra.MatrixExponent.Upper.Character.PermutationPowers
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse.Law
import OAI.LinearAlgebra.MatrixExponent.Rectangle.CharacterRank
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Weights
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Mask
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Rows

section
/-! # A mean bound for a shared label, including zero branches -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Upper Upper.TensorClass OAI.MatrixMultiplication.Foundation

theorem tag_nonneg (f : Character) {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    {n : ℕ} (A : Fin n → Tensor Coeff X Y Z) (hp : 0 < f.pX) :
    (∑ i, (f (ofTensor (A i)) : ℝ) ^ (1 / f.pX)) ^ f.pX ≤
      (f (ofTensor (Separation.shared A)) : ℝ) := by
  induction n with
  | zero => simp [Real.zero_rpow hp.ne']
  | succ n ih =>
    by_cases h : ∀ i, 0 < (f (ofTensor (A i)) : ℝ)
    · exact f.shared_tag_optimized_of_pos (Nat.succ_pos _) A h hp
    push Not at h
    obtain ⟨i, hi⟩ := h
    have hi' : (f (ofTensor (A i)) : ℝ) = 0 := le_antisymm hi (by positivity)
    rw [Fin.sum_univ_succAbove _ i, hi', Real.zero_rpow (by positivity), zero_add]
    apply (ih (fun j => A (i.succAbove j))).trans
    apply NNReal.coe_le_coe.mpr
    apply f.monotone'
    apply ofTensor_le
    let y (p : Fin n × Y) := (i.succAbove p.1, p.2)
    let z (p : Fin n × Z) := (i.succAbove p.1, p.2)
    have he : Tensor.pullback id y z (Separation.shared A) =
        Separation.shared (fun j => A (i.succAbove j)) := by
      funext p q r
      simp [Tensor.pullback, Separation.shared, y, z]
    rw [← he]
    exact CoefficientTensor.Restricts.pullback _ _ _ _

/-- The character value of a tagged family dominates the average value
of a branch times the value of a pairing of size `n`. -/
theorem meanTag (f : Character) {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    {n : ℕ} (hn : 0 < n) (A : Fin n → Tensor Coeff X Y Z) :
    (n : ℝ) ^ f.pX * (∑ i, (f (ofTensor (A i)) : ℝ)) ≤
      n * (f (ofTensor (Separation.shared A)) : ℝ) := by
  rcases eq_or_lt_of_le f.pX_nonneg with hp | hp
  · rw [← hp, Real.rpow_zero, one_mul]
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => NNReal.coe_le_coe.mpr
      (f.shared_branch_le A i))
  let v i := (f (ofTensor (A i)) : ℝ)
  have hv i : 0 ≤ v i := (f (ofTensor (A i))).coe_nonneg
  have hsum : 0 ≤ ∑ i, v i := Finset.sum_nonneg (fun i _ => hv i)
  have hpow : 0 ≤ ∑ i, v i ^ (1 / f.pX) := Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hv i) _)
  have hq : 1 ≤ 1 / f.pX := (le_div_iff₀ hp).mpr (by simpa using f.pX_le_one)
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Finset.univ hq (fun i _ => hv i)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have h' := Real.rpow_le_rpow (Real.rpow_nonneg hsum _) h hp.le
  rw [← Real.rpow_mul hsum, one_div_mul_cancel hp.ne', Real.rpow_one,
    Real.mul_rpow (by positivity) hpow, ← Real.rpow_mul (by positivity),
    show (1 / f.pX - 1) * f.pX = 1 - f.pX by field_simp] at h'
  calc
    _ ≤ (n : ℝ) ^ f.pX * ((n : ℝ) ^ (1 - f.pX) * (∑ i, v i ^ (1 / f.pX)) ^ f.pX) :=
      mul_le_mul_of_nonneg_left h' (by positivity)
    _ = (n : ℝ) * (∑ i, v i ^ (1 / f.pX)) ^ f.pX := by
      rw [← mul_assoc, ← Real.rpow_add (by positivity), add_sub_cancel, Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left (tag_nonneg f A hp) (by positivity)

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-! # Shared-label inequality for probability vectors allowing empty branches -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Upper Upper.TensorClass OAI.MatrixMultiplication.Foundation

theorem gibbs {n : ℕ} {q p : Fin n → ℝ}
    (hq : ∀ i, 0 ≤ q i) (hs : ∑ i, q i = 1) (hp : ∀ i, 0 ≤ p i)
    (hs' : ∑ i, p i ≤ 1) (hv : ∀ i, 0 < q i → 0 < p i) :
    ∑ i, q i * (Real.log (p i) - Real.log (q i)) ≤ 0 := by
  calc
    _ ≤ ∑ i, (p i - q i) := by
      apply Finset.sum_le_sum
      intro i _
      rcases eq_or_lt_of_le (hq i) with h | h
      · simp [← h, hp i]
      have he := Real.log_le_sub_one_of_pos (div_pos (hv i h) h)
      rw [Real.log_div (hv i h).ne' h.ne'] at he
      have := mul_le_mul_of_nonneg_left he h.le
      rw [mul_sub (q i) (_ / _), mul_div_cancel₀ _ h.ne', mul_one] at this
      exact this
    _ ≤ 0 := by rw [Finset.sum_sub_distrib, hs]; linarith

theorem entropy_log_card {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hs : ∑ i, q i = 1) :
    -(∑ i, q i * Real.log (q i)) ≤ Real.log n := by
  have he := gibbs (p := fun _ => (n : ℝ)⁻¹) hq hs (fun _ => by positivity)
    (by simp [hn.ne']) (fun _ _ => by positivity)
  simp only [Real.log_inv, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul] at he
  linarith

theorem logTag (f : Character) {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    {n : ℕ} (A : Fin n → Tensor Coeff X Y Z) (q : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hs : ∑ i, q i = 1) (hv : ∀ i, 0 < q i → 0 < (f (ofTensor (A i)) : ℝ)) :
    0 < (f (ofTensor (Separation.shared A)) : ℝ) ∧
    ∑ i, q i * (Real.log (f (ofTensor (A i))) - f.pX * Real.log (q i)) ≤
      Real.log (f (ofTensor (Separation.shared A))) := by
  let v i := (f (ofTensor (A i)) : ℝ)
  let V := (f (ofTensor (Separation.shared A)) : ℝ)
  have hv₀ i : 0 ≤ v i := NNReal.coe_nonneg _
  have hb i : v i ≤ V := NNReal.coe_le_coe.mpr (f.shared_branch_le A i)
  have hV : 0 < V := by
    by_contra! h
    have h' i : q i ≤ 0 := le_of_not_gt fun hi => (hv i hi).not_ge ((hb i).trans h)
    have := Finset.sum_nonpos (s := Finset.univ) (fun i _ => h' i)
    linarith
  refine ⟨hV, ?_⟩
  change ∑ i, q i * (Real.log (v i) - f.pX * Real.log (q i)) ≤ Real.log V
  rcases eq_or_lt_of_le f.pX_nonneg with hd | hd
  · calc
      _ ≤ ∑ i, q i * Real.log V := by
        apply Finset.sum_le_sum
        intro i _
        rcases eq_or_lt_of_le (hq i) with h | h
        · simp [← h]
        rw [← hd, zero_mul, sub_zero]
        exact mul_le_mul_of_nonneg_left (Real.log_le_log (hv i h) (hb i)) h.le
      _ = _ := by rw [← Finset.sum_mul, hs, one_mul]
  let p i := (v i / V) ^ (1 / f.pX)
  have hp i : 0 ≤ p i := Real.rpow_nonneg (div_nonneg (hv₀ i) hV.le) _
  have hp' i (h : 0 < q i) : 0 < p i := Real.rpow_pos_of_pos (div_pos (hv i h) hV) _
  have hsum : ∑ i, p i ≤ 1 := by
    have h₀ : 0 ≤ ∑ i, (v i) ^ (1 / f.pX) :=
      Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hv₀ i) _
    have he := Real.rpow_le_rpow (Real.rpow_nonneg h₀ _) (tag_nonneg f A hd)
      (by positivity : 0 ≤ 1 / f.pX)
    rw [← Real.rpow_mul h₀, mul_one_div_cancel hd.ne', Real.rpow_one] at he
    simp only [p, Real.div_rpow (hv₀ _) hV.le, ← Finset.sum_div]
    exact (div_le_one (by positivity)).mpr he
  have hl := gibbs hq hs hp hsum hp'
  calc
    _ = ∑ i, (q i * Real.log V + f.pX * (q i * (Real.log (p i) - Real.log (q i)))) := by
      apply Finset.sum_congr rfl
      intro i _
      rcases eq_or_lt_of_le (hq i) with h | h
      · simp [← h]
      have hi : 0 < v i := hv i h
      rw [show Real.log (p i) = 1 / f.pX * (Real.log (v i) - Real.log V) by
        unfold p; rw [Real.log_rpow (by positivity), Real.log_div hi.ne' hV.ne']]
      field_simp
      ring
    _ ≤ Real.log V := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hs, one_mul, ← Finset.mul_sum]
      exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hd.le hl)

theorem uniformTag (f : Character) {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    {n : ℕ} (A : Fin n → Tensor Coeff X Y Z) (s : Finset (Fin n)) (hs : s.Nonempty)
    {t : ℝ} (hv : ∀ i ∈ s, 0 < (f (ofTensor (A i)) : ℝ) ∧ t ≤ Real.log (f (ofTensor (A i)))) :
    0 < (f (ofTensor (Separation.shared A)) : ℝ) ∧
      t + f.pX * Real.log s.card ≤ Real.log (f (ofTensor (Separation.shared A))) := by
  classical
  let q i := if i ∈ s then (s.card : ℝ)⁻¹ else 0
  have hq (i) : 0 ≤ q i := by unfold q; positivity
  have hsum : ∑ i, q i = 1 := by simp [q, hs.card_pos.ne']
  have hpos {i} (h : 0 < q i) : i ∈ s := by by_contra hi; simp [q, hi] at h
  obtain ⟨hp, he⟩ := logTag f A q hq hsum (fun i h => (hv i (hpos h)).1)
  refine ⟨hp, le_trans ?_ he⟩
  have heq : t + f.pX * Real.log s.card = ∑ i, q i * (t + f.pX * Real.log s.card) := by
    rw [← Finset.sum_mul, hsum, one_mul]
  rw [heq]
  apply Finset.sum_le_sum
  intro i _
  rcases eq_or_lt_of_le (hq i) with h | h
  · rw [← h, zero_mul, zero_mul]
  apply mul_le_mul_of_nonneg_left _ h.le
  have hi := hpos h
  simp only [q, ite_eq_left hi, Real.log_inv]
  linarith [(hv i hi).2]

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

/-! # Reading colors visible on two legs of a weighted product -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
open Upper Upper.TensorClass OAI.MatrixMultiplication.Foundation

variable {X Y Z X' Y' Z' : Type} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']

theorem scaled_pullback (T : Tensor Coeff X Y Z) (a : X' → X) (b : Y' → Y) (c : Z' → Z)
    (α : X' → Coeff) (β : Y' → Coeff) (γ : Z' → Coeff) :
    ofTensor (fun x y z => α x * β y * γ z * T (a x) (b y) (c z)) ≤ ofTensor T := by
  classical
  apply ofTensor_le
  obtain ⟨A, B, C, he⟩ := CoefficientTensor.Restricts.pullback T a b c
  refine ⟨fun x i => α x * A x i, fun y j => β y * B y j, fun z k => γ z * C z k, ?_⟩
  rw [Separation.restrict_scaled, ← he]
  rfl

private theorem read_label (T : Tensor Coeff X Y Z) (f : Character) {n : ℕ} (hn : 0 < n)
    (a : Y → Fin n) (b : Z → Fin n) (h : ∀ x y z, T x y z ≠ 0 → a y = b z)
    (A : Fin n → Tensor Coeff X Y Z)
    (hA : ∀ i x y z, A i x y z = if a y = i then T x y z else 0) :
    (n : ℝ) ^ f.pX * ∑ i, (f (ofTensor (A i)) : ℝ) ≤ n * (f (ofTensor T) : ℝ) := by
  classical
  have he := scaled_pullback T id (Prod.snd : Fin n × Y → Y) (Prod.snd : Fin n × Z → Z)
    (fun _ => 1) (fun y => if a y.2 = y.1 then 1 else 0) (fun z => if b z.2 = z.1 then 1 else 0)
  have hs : ofTensor (Separation.shared A) ≤ ofTensor T := by
    convert he using 1
    congr 1
    funext x y z
    simp only [Separation.shared, hA, id_eq]
    by_cases hz : T x y.2 z.2 = 0
    · simp [hz]
    rw [← h _ _ _ hz]
    grind
  exact (meanTag f hn A).trans (mul_le_mul_of_nonneg_left
    (NNReal.coe_le_coe.mpr (f.monotone' hs)) (by positivity))

abbrev Table (F : Type*) (i j k : ℕ) := Fin i → Fin j → Fin k → F
variable {i j k n : ℕ}

def coeff (w : Table Coeff i j k) : Tensor Coeff (Pos i k) (Pos k j) (Pos i j) :=
  fun x y z => if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then w x.1 y.2 x.2 else 0

def price (f : Character) (w : Table Coeff i j k) : ℝ := f (ofTensor (coeff w))

def byRow (a : Fin i → Fin n) (w : Table Coeff i j k) (d : Fin n) : Table Coeff i j k :=
  fun x y z => if a x = d then w x y z else 0

def byCol (a : Fin j → Fin n) (w : Table Coeff i j k) (d : Fin n) : Table Coeff i j k :=
  fun x y z => if a y = d then w x y z else 0

def byKey (a : Fin k → Fin n) (w : Table Coeff i j k) (d : Fin n) : Table Coeff i j k :=
  fun x y z => if a z = d then w x y z else 0

theorem read_col (f : Character) (w : Table Coeff i j k) (a : Fin j → Fin n) (hn : 0 < n) :
    (n : ℝ) ^ f.pX * ∑ t, price f (byCol a w t) ≤ n * price f w := by
  apply read_label (coeff w) f hn (fun y => a y.2) (fun z => a z.2) _
    (fun t => coeff (byCol a w t)) <;> intros <;> grind [coeff, byCol]

theorem read_row (f : Character) (w : Table Coeff i j k) (a : Fin i → Fin n) (hn : 0 < n) :
    (n : ℝ) ^ f.pY * ∑ t, price f (byRow a w t) ≤ n * price f w := by
  let T (w : Table Coeff i j k) := CoefficientTensor.swapXY (coeff w)
  have he (w : Table Coeff i j k) : (f.permuted 1 (ofTensor (T w)) : ℝ) = price f w := rfl
  have h := read_label (T w) (f.permuted 1) hn (fun x => a x.1) (fun z => a z.1)
    (by intros; unfold T at *; grind [coeff, CoefficientTensor.swapXY])
    (fun t => T (byRow a w t)) (by intros; unfold T at *; grind [coeff, byRow, CoefficientTensor.swapXY])
  simpa only [he, show (f.permuted 1).pX = f.pY by rw [f.permuted_pX]; rfl] using h

theorem read_key (f : Character) (w : Table Coeff i j k) (a : Fin k → Fin n) (hn : 0 < n) :
    (n : ℝ) ^ f.pZ * ∑ t, price f (byKey a w t) ≤ n * price f w := by
  let T (w : Table Coeff i j k) := CoefficientTensor.swapXY (CoefficientTensor.swapYZ (coeff w))
  have he (w : Table Coeff i j k) : (f.permuted 4 (ofTensor (T w)) : ℝ) = price f w := rfl
  have h := read_label (T w) (f.permuted 4) hn (fun x => a x.2) (fun y => a y.1)
    (by intros; unfold T at *; grind [coeff, CoefficientTensor.swapXY, CoefficientTensor.swapYZ])
    (fun t => T (byKey a w t))
    (by intros; unfold T at *; grind [coeff, byKey, CoefficientTensor.swapXY, CoefficientTensor.swapYZ])
  simpa only [he, show (f.permuted 4).pX = f.pZ by rw [f.permuted_pX]; rfl] using h

theorem price_rank (f : Character) {w : Table Coeff i j k} {r : ℕ}
    (h : WeightedRankLE w r) : price f w ≤ r := by
  have hr : Tensor.RankAtMost (coeff w) r := by
    obtain ⟨a, b, c, he⟩ := h
    exact ⟨a, b, c, funext fun x => funext fun y => funext fun z => (he x y z).symm⟩
  have he := f.le_rank (ofTensor (coeff w))
  rw [rank_ofTensor] at he
  exact_mod_cast he.trans (Nat.cast_le.mpr ((CoefficientTensor.rank_le_iff _ _).mpr hr))

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
end

section
/-! # Extracting a diagonal from isolated triples -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
open Upper Upper.TensorClass OAI.MatrixMultiplication.Foundation

variable {i j k : ℕ}

theorem diagonal_price (f : Character) (w : Table Coeff i j k) (S : Finset (Cell i j k))
    (hs : ∀ t ∈ S, w t.1 t.2.1 t.2.2 ≠ 0)
    (ha : ∀ t ∈ S, ∀ x, w x t.2.1 t.2.2 ≠ 0 → x = t.1)
    (hb : ∀ t ∈ S, ∀ y, w t.1 y t.2.2 ≠ 0 → y = t.2.1)
    (hc : ∀ t ∈ S, ∀ z, w t.1 t.2.1 z ≠ 0 → z = t.2.2) :
    (S.card : ℝ) ≤ price f w := by
  classical
  let T : Fin S.card ≃ S := (Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm
  let a l := (T l).val.1
  let b l := (T l).val.2.1
  let c l := (T l).val.2.2
  have hinj (x y : Fin S.card) (h₁ : a x = a y) (h₂ : b x = b y) (h₃ : c x = c y) : x = y :=
    T.injective (Subtype.ext (Prod.ext h₁ (Prod.ext h₂ h₃)))
  have he : (fun x y z => (w (a x) (b x) (c x))⁻¹ * 1 * 1 *
      coeff w (a x, c x) (c y, b y) (a z, b z)) = CoefficientTensor.natTensor S.card := by
    funext x y z
    simp only [coeff, CoefficientTensor.natTensor, mul_one]
    by_cases h : x = y ∧ x = z
    · obtain ⟨rfl, rfl⟩ := h
      simp [show w (a x) (b x) (c x) ≠ 0 from hs _ (T x).property]
    rw [ite_eq_right h]
    split_ifs with hh
    · have hz : w (a x) (b y) (c x) = 0 := by
        by_contra h'
        have hh₁ : a x = a y := ha _ (T y).property _ (by rw [hh.2.1] at h'; exact h')
        have hh₂ : b y = b x := hb _ (T x).property _ h'
        have hh₃ : c x = c z := hc _ (T z).property _ (by rw [hh.1, hh.2.2] at h'; exact h')
        exact h ⟨hinj x y hh₁ hh₂.symm hh.2.1, hinj x z hh.1 (hh₂.symm.trans hh.2.2) hh₃⟩
      rw [hz, mul_zero]
    · rw [mul_zero]
  have h := scaled_pullback (coeff w) (fun x => (a x, c x)) (fun y => (c y, b y))
    (fun z => (a z, b z)) (fun x => (w (a x) (b x) (c x))⁻¹) (fun _ => 1) (fun _ => 1)
  rw [he, ← natCast_eq_ofTensor_natTensor] at h
  have hr := f.monotone' h
  change f.toHom (S.card : TensorClass) ≤ _ at hr
  rw [map_natCast] at hr
  exact_mod_cast hr

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
end

/-! # A price bound for triples with bounded completion counts -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
open Upper Upper.TensorClass Finset

variable {i j k I J K : ℕ}
    (a : Fin i → Fin I) (b : Fin j → Fin J) (c : Fin k → Fin K) (w : Table Coeff i j k)

private def key (t : Cell i j k) : Cell I J K := (a t.1, b t.2.1, c t.2.2)

private def bucket (t : Cell I J K) := byKey c (byCol b (byRow a w t.1) t.2.1) t.2.2

private theorem bucket_iff (s : Cell I J K) (x y z) :
    bucket a b c w s x y z ≠ 0 ↔ (x, y, z) ∈ support w ∧ key a b c (x, y, z) = s := by
  simp only [bucket, byKey, byCol, byRow, key, support, mem_filter, mem_univ, true_and, Prod.ext_iff]
  grind

private theorem read_all (f : Character) (hI : 0 < I) (hJ : 0 < J) (hK : 0 < K) :
    (I : ℝ) ^ f.pY * (J : ℝ) ^ f.pX * (K : ℝ) ^ f.pZ * (∑ s, price f (bucket a b c w s)) ≤
      (I : ℝ) * J * K * price f w := by
  have h₁ := read_row f w a hI
  have h₂ := sum_le_sum (s := univ) (fun t _ => read_col f (byRow a w t) b hJ)
  have h₃ := sum_le_sum (s := univ) fun s _ =>
    sum_le_sum (s := univ) fun t _ => read_key f (byCol b (byRow a w s) t) c hK
  simp only [← mul_sum] at h₂ h₃
  simp only [Fintype.sum_prod_type, bucket]
  linarith only [mul_le_mul_of_nonneg_left h₁ (by positivity : 0 ≤ (J : ℝ) * K),
    mul_le_mul_of_nonneg_left h₂ (by positivity : 0 ≤ (I : ℝ) ^ f.pY * K),
    mul_le_mul_of_nonneg_left h₃ (by positivity : 0 ≤ (I : ℝ) ^ f.pY * (J : ℝ) ^ f.pX)]

private theorem isolate (f : Character) (V : Finset (Cell i j k)) (hs : V ⊆ support w)
    (ha : ∀ t ∈ V, ∀ x ∈ rows (support w) t, a x = a t.1 → x = t.1)
    (hb : ∀ t ∈ V, ∀ y ∈ cols (support w) t, b y = b t.2.1 → y = t.2.1)
    (hc : ∀ t ∈ V, ∀ z ∈ inner (support w) t, c z = c t.2.2 → z = t.2.2) :
    (V.card : ℝ) ≤ ∑ s, price f (bucket a b c w s) := by
  classical
  let W s := V.filter (fun t => key a b c t = s)
  have hh (s) : ((W s).card : ℝ) ≤ price f (bucket a b c w s) := by
    apply diagonal_price
    · intro t ht
      exact (bucket_iff _ _ _ _ _ _ _ _).mpr ⟨hs (mem_filter.mp ht).1, (mem_filter.mp ht).2⟩
    · intro t ht x hx
      obtain ⟨ht, he⟩ := mem_filter.mp ht
      obtain ⟨hx, hx'⟩ := (bucket_iff _ _ _ _ _ _ _ _).mp hx
      exact ha t ht x (mem_filter.mpr ⟨mem_univ _, hx⟩) (congrArg Prod.fst (hx'.trans he.symm))
    · intro t ht y hy
      obtain ⟨ht, he⟩ := mem_filter.mp ht
      obtain ⟨hy, hy'⟩ := (bucket_iff _ _ _ _ _ _ _ _).mp hy
      exact hb t ht y (mem_filter.mpr ⟨mem_univ _, hy⟩) (congrArg (fun u => u.2.1) (hy'.trans he.symm))
    · intro t ht z hz
      obtain ⟨ht, he⟩ := mem_filter.mp ht
      obtain ⟨hz, hz'⟩ := (bucket_iff _ _ _ _ _ _ _ _).mp hz
      exact hc t ht z (mem_filter.mpr ⟨mem_univ _, hz⟩) (congrArg (fun u => u.2.2) (hz'.trans he.symm))
  have he : ∑ s, (W s).card = V.card := by
    simpa [W] using sum_fiberwise V (key a b c) (fun _ => (1 : ℕ))
  rw [← he, Nat.cast_sum]
  exact sum_le_sum fun s _ => hh s

theorem colored {r : ℕ} (hr : WeightedRankLE w r) (f : Character)
    (U : Finset (Cell i j k)) (hu : U ⊆ support w) (hI : 0 < I) (hJ : 0 < J) (hK : 0 < K)
    (h₁ : ∀ t ∈ U, (rows (support w) t).card ≤ I)
    (h₂ : ∀ t ∈ U, (cols (support w) t).card ≤ J)
    (h₃ : ∀ t ∈ U, (inner (support w) t).card ≤ K) :
    (I : ℝ) ^ f.pY * (J : ℝ) ^ f.pX * (K : ℝ) ^ f.pZ * U.card ≤ 432 * (I : ℝ) * J * K * r := by
  obtain ⟨a, b, c, V, hv, hv', ha, hb, hc⟩ := color (support w) U hI hJ hK h₁ h₂ h₃
  have he := read_all a b c w f (by positivity) (by positivity) (by positivity)
  have hl := isolate a b c w f V (hv.trans hu) ha hb hc
  have hV : (U.card : ℝ) ≤ 2 * V.card := by exact_mod_cast hv'
  have hbound (n : ℕ) (x : ℝ) (hx : 0 ≤ x) : (n : ℝ) ^ x ≤ (6 * n : ℕ) ^ x :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast (by omega : n ≤ 6 * n)) hx
  have hs : (I : ℝ) ^ f.pY * (J : ℝ) ^ f.pX * (K : ℝ) ^ f.pZ * V.card ≤
      (6 * I : ℕ) * (6 * J : ℕ) * (6 * K : ℕ) * (r : ℝ) := by
    refine (le_trans ?_ he).trans ?_
    · exact mul_le_mul (mul_le_mul (mul_le_mul (hbound I _ f.pY_nonneg) (hbound J _ f.pX_nonneg)
        (by positivity) (by positivity)) (hbound K _ f.pZ_nonneg) (by positivity) (by positivity))
        hl (by positivity) (by positivity)
    · exact mul_le_mul_of_nonneg_left (price_rank f hr) (by positivity)
  push_cast at hs
  linarith only [hs, mul_le_mul_of_nonneg_left hV (by positivity : 0 ≤ (I : ℝ) ^ f.pY * (J : ℝ) ^ f.pX * (K : ℝ) ^ f.pZ)]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
end

/-!
# Reading the three labels of a weighted product

Each label is visible on two legs. At each level the shared-tag bound
dominates the arithmetic mean of the child prices times the price of
that wire. Thus every nonzero leaf contributes the same lower bound,
regardless of the coefficient.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Upper Upper.TensorClass OAI.MatrixMultiplication.Foundation

variable {i j k : ℕ} (w : Fin i → Fin j → Fin k → Coeff)

def leaf (a : Fin i) (b : Fin j) (c : Fin k) : Tensor Coeff Unit Unit Unit :=
  fun _ _ _ => w a b c

def inner (b : Fin j) (a : Fin i) :=
  CoefficientTensor.swapYZ (CoefficientTensor.swapXY (Upper.Separation.shared (leaf w a b)))

def rows (b : Fin j) := CoefficientTensor.swapXY (Upper.Separation.shared (inner w b))

def allRows := Upper.Separation.shared (rows w)

theorem price_le_rank (f : Character) {r : ℕ} (h : WeightedRankLE w r) :
    (f (ofTensor (allRows w)) : ℝ) ≤ r := by
  have hr : Tensor.RankAtMost (allRows w) r := by
    obtain ⟨a, b, c, he⟩ := h
    refine ⟨fun l x => a l (x.1, x.2.1), fun l y => b l (y.2.1, y.1),
      fun l z => c l (z.2.1, z.1), ?_⟩
    funext x y z
    simp only [Tensor.rankOne]
    rw [he]
    simp only [allRows, rows, inner, leaf, Upper.Separation.shared, CoefficientTensor.swapXY,
      CoefficientTensor.swapYZ]
    grind
  have hb := f.le_rank (ofTensor (allRows w))
  rw [rank_ofTensor] at hb
  exact_mod_cast hb.trans (Nat.cast_le.mpr ((CoefficientTensor.rank_le_iff _ _).mpr hr))

private theorem combine (f : Character) {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    {n : ℕ} (hn : 0 < n) (A : Fin n → Tensor Coeff X Y Z) (m : Fin n → ℕ)
    {p q : ℝ} (hq : 0 ≤ q) (h : ∀ i, (m i : ℝ) * p ≤ q * (f (ofTensor (A i)) : ℝ)) :
    (∑ i, m i : ℕ) * (p * (n : ℝ) ^ f.pX) ≤ (q * n) * (f (ofTensor (Upper.Separation.shared A)) : ℝ) := by
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← Nat.cast_sum] at he
  have ht := mul_le_mul_of_nonneg_left (meanTag f hn A) hq
  linarith only [ht, mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ (n : ℝ) ^ f.pX)]

private theorem density_price (f : Character) (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
    supportSize w * ((j : ℝ) ^ f.pX * (i : ℝ) ^ f.pY * (k : ℝ) ^ f.pZ) ≤
      (i : ℝ) * j * k * (f (ofTensor (allRows w)) : ℝ) := by
  classical
  let bit (b : Fin j) (a : Fin i) (c : Fin k) := if w a b c = 0 then 0 else 1
  have hleaf (b : Fin j) (a : Fin i) (c : Fin k) :
      (bit b a c : ℝ) * 1 ≤ 1 * (f.permuted 5 (ofTensor (leaf w a b c)) : ℝ) := by
    unfold bit
    split_ifs with h
    · simp
    · have he : leaf w a b c ≠ 0 := fun he => h (congrFun (congrFun (congrFun he ()) ()) ())
      simpa only [Nat.cast_one, one_mul] using
        (show (1 : ℝ) ≤ f.permuted 5 (ofTensor (leaf w a b c)) by
          exact_mod_cast (f.permuted 5).one_le_of_tensor_ne_zero _ he)
  have hk' (b : Fin j) (a : Fin i) :
      (∑ c, bit b a c : ℕ) * (k : ℝ) ^ f.pZ ≤ k * (f.permuted 1 (ofTensor (inner w b a)) : ℝ) := by
    have he := combine (f.permuted 5) hk (leaf w a b) (bit b a) (by norm_num) (hleaf b a)
    rw [show (f.permuted 5).pX = f.pZ by rw [f.permuted_pX]; rfl, one_mul, one_mul] at he
    exact he
  have hi' (b : Fin j) :
      (∑ a, ∑ c, bit b a c : ℕ) * ((k : ℝ) ^ f.pZ * (i : ℝ) ^ f.pY) ≤
        ((k : ℝ) * i) * (f (ofTensor (rows w b)) : ℝ) := by
    have he := combine (f.permuted 1) hi (inner w b) (fun a => ∑ c, bit b a c)
      (by positivity) (hk' b)
    rw [show (f.permuted 1).pX = f.pY by rw [f.permuted_pX]; rfl] at he
    exact he
  have he := combine f hj (rows w) (fun b => ∑ a, ∑ c, bit b a c) (by positivity) hi'
  change supportSize w * ((k : ℝ) ^ f.pZ * (i : ℝ) ^ f.pY * (j : ℝ) ^ f.pX) ≤
    (k : ℝ) * i * j * (f (ofTensor (allRows w)) : ℝ) at he
  linarith only [he]

private theorem size_le : supportSize w ≤ i * j * k := by
  classical
  unfold supportSize
  calc
    _ ≤ ∑ _ : Fin j, ∑ _ : Fin i, ∑ _ : Fin k, (1 : ℕ) := by
      gcongr
      split <;> omega
    _ = _ := by simp [mul_comm, mul_left_comm]

private theorem size_zero (h : WeightedRankLE w 0) : supportSize w = 0 := by
  obtain ⟨a, b, c, h⟩ := h
  have hz (x y z) : w x y z = 0 := by simpa using (h (x, z) (z, y) (x, y)).symm
  simp [supportSize, hz]

theorem coeff_density : DensityBound Coeff := by
  intro i j k r hi hj hk w hr
  rcases eq_or_lt_of_le (Nat.zero_le (supportSize w)) with h | h
  · rw [← h, Nat.cast_zero, zero_mul]
    positivity
  have hsize : 0 < (supportSize w : ℝ) := by exact_mod_cast h
  have hr' : 1 ≤ r := Nat.pos_of_ne_zero fun he => h.ne' (size_zero w (he ▸ hr))
  let s := (i : ℝ) * j * k * r / supportSize w
  have hs : 1 ≤ s := (one_le_div hsize).2 (by
    exact_mod_cast (size_le w).trans (Nat.le_mul_of_pos_right _ hr'))
  have hi' : 1 ≤ (i : ℝ) := by exact_mod_cast hi
  have hj' : 1 ≤ (j : ℝ) := by exact_mod_cast hj
  have hk' : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hL : exponent Coeff (Real.log i) (Real.log j) (Real.log k) ≤ Real.log s := by
    apply exponent_le_of_characters (Real.log_nonneg hi') (Real.log_nonneg hj')
      (Real.log_nonneg hk') (Real.log_nonneg hs)
    intro f
    apply (Real.le_log_iff_exp_le (by positivity)).2
    rw [Real.exp_add, Real.exp_add, ← Real.rpow_def_of_pos (by positivity),
      ← Real.rpow_def_of_pos (by positivity), ← Real.rpow_def_of_pos (by positivity)]
    apply (le_div_iff₀ hsize).mpr
    rw [mul_comm]
    exact (density_price w f hi hj hk).trans
      (mul_le_mul_of_nonneg_left (price_le_rank w f hr) (by positivity))
  rw [mul_comm]
  apply (le_div_iff₀ hsize).mp
  exact (Real.le_log_iff_exp_le (zero_lt_one.trans_le hs)).mp hL

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

/-!
# Sparse sets of output cells

Read the column first, with probability proportional to its degree.
The log of the cell count splits into column entropy and average log
degree. Each part is bounded by the log of its alphabet size. The
spectral formula and transposition can only lower the arithmetic
exponent when balancing these two parts.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Upper Upper.TensorClass

variable {i j k r : ℕ} (u : Finset (Pos i j))

private def column (b : Fin j) := Finset.univ.filter fun a : Fin i => (a, b) ∈ u

private theorem sum_column : ∑ b, (column u b).card = u.card := by
  classical
  simp only [column, Finset.card_filter]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type (fun p : Pos i j => if p ∈ u then 1 else 0)]
  simp

private def prob (b : Fin j) := (column u b).card / (u.card : ℝ)
private def width := ∑ b, prob u b * Real.log (column u b).card

private theorem prob_nonneg (b) : 0 ≤ prob u b := by unfold prob; positivity

private theorem prob_sum (hu : u.Nonempty) : ∑ b, prob u b = 1 := by
  simp only [prob, ← Finset.sum_div, ← Nat.cast_sum, sum_column]
  exact div_self (by exact_mod_cast hu.card_pos.ne')

private theorem column_pos {b} (h : 0 < prob u b) : (column u b).Nonempty := by
  by_contra! he
  simp [prob, he] at h

private theorem entropy_eq (hu : u.Nonempty) :
    -(∑ b, prob u b * Real.log (prob u b)) = Real.log u.card - width u := by
  have he (b) : prob u b * Real.log (prob u b) =
      prob u b * Real.log (column u b).card - prob u b * Real.log u.card := by
    rcases eq_or_lt_of_le (prob_nonneg u b) with hb | hb
    · simp [← hb]
    have hc := (column_pos u hb).card_pos
    have hd := hu.card_pos
    unfold prob
    rw [Real.log_div (by positivity) (by positivity), mul_sub]
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, prob_sum u hu, one_mul, neg_sub]
  rfl

private theorem width_bounds (hu : u.Nonempty) (hj : 0 < j) :
    0 ≤ width u ∧ width u ≤ Real.log i ∧ 0 ≤ Real.log u.card - width u ∧
      Real.log u.card - width u ≤ Real.log j := by
  have hq := prob_nonneg u
  have hs := prob_sum u hu
  have hw₀ : 0 ≤ width u := by
    apply Finset.sum_nonneg
    intro b _
    rcases eq_or_lt_of_le (hq b) with h | h
    · simp [← h]
    exact mul_nonneg h.le (Real.log_nonneg (by exact_mod_cast (column_pos u h).card_pos))
  have hw : width u ≤ Real.log i := by
    calc
      _ ≤ ∑ b, prob u b * Real.log i := by
        apply Finset.sum_le_sum
        intro b _
        rcases eq_or_lt_of_le (hq b) with h | h
        · simp [← h]
        apply mul_le_mul_of_nonneg_left _ h.le
        refine Real.log_le_log (by exact_mod_cast (column_pos u h).card_pos) ?_
        exact_mod_cast (show (column u b).card ≤ i by simpa using (column u b).card_le_univ)
      _ = _ := by rw [← Finset.sum_mul, hs, one_mul]
  rw [← entropy_eq u hu]
  refine ⟨hw₀, hw, neg_nonneg.mpr (Finset.sum_nonpos ?_), entropy_log_card hj _ hq hs⟩
  intro b _
  have he : prob u b ≤ 1 := hs ▸ Finset.single_le_sum (fun a _ => hq a) (Finset.mem_univ b)
  exact mul_nonpos_of_nonneg_of_nonpos (hq b) (Real.log_nonpos (hq b) he)

variable {w : Fin i → Fin j → Fin k → Coeff}

private theorem row_price (f : Character) (hk : 0 < k)
    (hw : ∀ x y z, w x y z ≠ 0 ↔ (x, y) ∈ u) {b : Fin j} (hb : 0 < prob u b) :
    0 < (f (ofTensor (rows w b)) : ℝ) ∧
    f.pZ * Real.log k + f.pY * Real.log (column u b).card ≤ Real.log (f (ofTensor (rows w b))) := by
  have hf (a : Fin i) (ha : a ∈ column u b) :
      0 < (f.permuted 1 (ofTensor (inner w b a)) : ℝ) ∧
      f.pZ * Real.log k ≤ Real.log (f.permuted 1 (ofTensor (inner w b a))) := by
    have hl (c : Fin k) (_ : c ∈ Finset.univ) :
        0 < (f.permuted 5 (ofTensor (leaf w a b c)) : ℝ) ∧
        0 ≤ Real.log (f.permuted 5 (ofTensor (leaf w a b c))) := by
      have hh : w a b c ≠ 0 := (hw a b c).2 (Finset.mem_filter.mp ha).2
      have hn : leaf w a b c ≠ 0 := fun he => hh (congrFun (congrFun (congrFun he ()) ()) ())
      have he : (1 : ℝ) ≤ f.permuted 5 (ofTensor (leaf w a b c)) := by
        exact_mod_cast (f.permuted 5).one_le_of_tensor_ne_zero _ hn
      exact ⟨zero_lt_one.trans_le he, Real.log_nonneg he⟩
    have he := uniformTag (f.permuted 5) (leaf w a b) Finset.univ
      ⟨⟨0, hk⟩, Finset.mem_univ _⟩ hl
    rw [show (f.permuted 5).pX = f.pZ by rw [f.permuted_pX]; rfl,
      Finset.card_univ, Fintype.card_fin, zero_add] at he
    exact he
  have he := uniformTag (f.permuted 1) (inner w b) _ (column_pos u hb) hf
  rw [show (f.permuted 1).pX = f.pY by rw [f.permuted_pX]; rfl] at he
  exact he

private theorem cell_price (f : Character) (hk : 0 < k) (hu : u.Nonempty)
    (hw : ∀ x y z, w x y z ≠ 0 ↔ (x, y) ∈ u) (hr : WeightedRankLE w r) :
    (Real.log u.card - width u) * f.pX + width u * f.pY + Real.log k * f.pZ ≤ Real.log r := by
  have hb {b : Fin j} := row_price u f hk hw (b := b)
  obtain ⟨hp, he⟩ := logTag f (rows w) (prob u) (prob_nonneg u) (prob_sum u hu)
    (fun b h => (hb h).1)
  refine le_trans ?_ (he.trans (Real.log_le_log hp (price_le_rank w f hr)))
  rw [← entropy_eq u hu]
  calc
    _ = ∑ b, (prob u b * Real.log (prob u b) * (-f.pX) +
        prob u b * Real.log (column u b).card * f.pY + prob u b * (Real.log k * f.pZ)) := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, prob_sum u hu, width]
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro b _
      rcases eq_or_lt_of_le (prob_nonneg u b) with h | h
      · simp [← h]
      linarith only [mul_le_mul_of_nonneg_left (hb h).2 h.le]

private theorem balance {F : Type} [Field F] {a b c t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (ht : min a b ≤ t) (ht' : t ≤ max a b) :
    exponent F t (a + b - t) c ≤ exponent F a b c := by
  have h₁ : 0 ≤ t := (le_min ha hb).trans ht
  have h₂ : 0 ≤ a + b - t := by linarith [max_le (le_add_of_nonneg_right hb) (le_add_of_nonneg_left ha)]
  obtain ⟨x, y, z, hp, he⟩ := (support F).attains h₁ h₂ hc
  have hab := (support F).bound ha hb hc hp
  have hba := (support F).bound hb ha hc hp
  rw [transpose F hb ha hc] at hba
  rw [← he]
  unfold load at *
  rcases le_total y z with h | h
  · rcases min_le_iff.mp ht with h' | h' <;>
      linarith only [hab, hba, mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr h')]
  · rcases le_max_iff.mp ht' with h' | h' <;>
      linarith only [hab, hba, mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr h')]

theorem coeff_cells : CellBound Coeff := by
  intro i j k r hi hj hk w u hu hw hr
  have hr' : 0 < r := by
    by_contra! hn
    have he : r = 0 := by omega
    subst r
    obtain ⟨_, _, _, h⟩ := hr
    obtain ⟨⟨a, b⟩, hab⟩ := hu
    let c : Fin k := ⟨0, hk⟩
    apply (hw a b c).mpr hab
    simpa using (h (a, c) (c, b) (a, b)).symm
  let a := width u
  let b := Real.log u.card - a
  have he : a + b = Real.log u.card := by unfold b; ring
  obtain ⟨ha, ha', hb, hb'⟩ := width_bounds u hu hj
  have hc : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  have hs : exponent Coeff a b (Real.log k) ≤ Real.log r :=
    exponent_le_of_characters ha hb hc (Real.log_nonneg (by exact_mod_cast hr'))
      (fun f => cell_price u f hk hu hw hr)
  have ht : min a b ≤ short i j u.card :=
    le_min (le_min ((min_le_left _ _).trans ha') ((min_le_right _ _).trans hb'))
      (by linarith [min_le_left a b, min_le_right a b])
  have ht' : short i j u.card ≤ max a b :=
    (min_le_right _ _).trans (by linarith [le_max_left a b, le_max_right a b])
  have hh := balance (F := Coeff) (a := a) (b := b) ha hb hc ht ht'
  rw [he] at hh
  exact (Real.le_log_iff_exp_le (by positivity)).mp (hh.trans hs)

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-! # Transferring the finite colored comparison to the arithmetic exponent -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
open Upper Upper.TensorClass

private theorem character_exists : Nonempty Character := by
  obtain ⟨f, hf, _⟩ := Spectrum.extension
    (fun _ _ _ h => add_mono h le_rfl) (fun _ _ _ h => mul_mono le_rfl h)
    TensorClass.zero_le (fun _ => one_le_of_ne_zero) (fun A => ⟨rank A, le_rank_natCast A⟩)
    (Nat.castRingHom TensorClass) (Nat.castRingHom NNReal)
    (fun m n h => Nat.cast_le.mpr ((natCast_le_natCast_iff m n).mp h))
  exact ⟨⟨f, hf⟩⟩

theorem coeff_degrees : DegreeBound Coeff := by
  intro i j k I J K r hI hJ hK w U hu h₁ h₂ h₃ hr
  rcases U.card.eq_zero_or_pos with h | h
  · rw [h, Nat.cast_zero, zero_mul]; positivity
  have hU : 0 < (U.card : ℝ) := by positivity
  let b := 432 * (I : ℝ) * J * K * r / U.card
  have hb (f : Character) :
      Real.exp (Real.log J * f.pX + Real.log I * f.pY + Real.log K * f.pZ) ≤ b := by
    apply (le_div_iff₀ hU).mpr
    rw [Real.exp_add, Real.exp_add, ← Real.rpow_def_of_pos (by positivity),
      ← Real.rpow_def_of_pos (by positivity), ← Real.rpow_def_of_pos (by positivity),
      mul_comm ((J : ℝ) ^ f.pX)]
    exact colored w hr f U hu hI hJ hK h₁ h₂ h₃
  have hl {m : ℕ} (hm : 0 < m) := Real.log_nonneg (by exact_mod_cast hm : 1 ≤ (m : ℝ))
  obtain ⟨f⟩ := character_exists
  have hpos : 1 ≤ b := le_trans (Real.one_le_exp (add_nonneg (add_nonneg
    (mul_nonneg (hl hJ) f.pX_nonneg) (mul_nonneg (hl hI) f.pY_nonneg))
    (mul_nonneg (hl hK) f.pZ_nonneg))) (hb f)
  have hp := zero_lt_one.trans_le hpos
  have he := exponent_le_of_characters (hl hI) (hl hJ) (hl hK) (Real.log_nonneg hpos)
    (fun f => (Real.le_log_iff_exp_le hp).mpr (hb f))
  rw [mul_comm]
  exact (le_div_iff₀ hU).mp ((Real.le_log_iff_exp_le hp).mp he)

theorem degrees_of_closed (h : ∀ (K : Type) [Field K] [IsAlgClosed K], DegreeBound K)
    (F : Type*) [Field F] : DegreeBound F := by
  intro i j k I J K r hI hJ hK w U hu h₁ h₂ h₃ hr
  obtain ⟨L, _, φ, v, hv, he⟩ := small_witness hr
  let _ : Algebra L F := φ.toAlgebra
  let ψ := algebraMap L (AlgebraicClosure L)
  have hs : support (fun x y z => ψ (v x y z)) = support w := by
    rw [← he]
    ext t
    simp [support]
  rw [← hs] at hu h₁ h₂ h₃
  have he := h (AlgebraicClosure L) i j k I J K r hI hJ hK _ U hu h₁ h₂ h₃ (hv.map ψ)
  have hl {n : ℕ} (hn : 0 < n) := Real.log_nonneg (by exact_mod_cast hn : 1 ≤ (n : ℝ))
  rw [exponent_extension L F (hl hI) (hl hJ) (hl hK)]
  rwa [exponent_extension L (AlgebraicClosure L) (hl hI) (hl hJ) (hl hK)] at he

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
end
