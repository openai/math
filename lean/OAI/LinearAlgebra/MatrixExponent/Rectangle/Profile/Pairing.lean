import OAI.LinearAlgebra.MatrixExponent.Spectral.Rank
import Mathlib.LinearAlgebra.Vandermonde
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Rows
import OAI.LinearAlgebra.MatrixExponent.Spectral.Wire
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup.Dense
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Border.Price
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile.Scale
import OAI.LinearAlgebra.MatrixExponent.Prices.Chord
import OAI.LinearAlgebra.MatrixExponent.Spectral.Place

/-!
# Polynomial multiplication with many input lengths

The output has the sum of the input lengths as its capacity. Extra
coordinates, if any, have zero coefficients.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Spectral Finset

variable {ι : Type} [Fintype ι]

def length (L : ι → ℕ) : Option ι → ℕ
  | none => ∑ i, L i
  | some i => L i

abbrev leg (L : ι → ℕ) (s : Option ι) := Fin (length L s)

variable (K : Type) [Field K] (L : ι → ℕ)

def entry (x : ∀ s, leg L s) : K := if ∑ i, (x (some i)).val = (x none).val then 1 else 0

def polynomial : Tensor K (Option ι) := Tensor.ofRaw (Raw.ofTable (leg L) (entry K L))

variable {L}

theorem polynomial_mono : Monotone (polynomial (ι := ι) K) := by
  intro L L' h
  have he (s) : length L s ≤ length L' s := by
    cases s with
    | none => exact sum_le_sum (fun i _ => h i)
    | some i => exact h i
  refine Raw.Restricts.pullback (fun s x => Fin.castLE (he s) x) ?_
  intro x
  change (∀ s, leg L s) at x
  refine (Raw.coeff_ofTable _ _ x).trans ?_
  exact (Raw.coeff_ofTable (leg L') (entry K L') (fun s => Fin.castLE (he s) (x s))).symm

theorem polynomial_ne_zero [Nonempty ι] (hL : ∀ i, 0 < L i) : polynomial K L ≠ 0 := by
  have hp (s) : 0 < length L s := by
    cases s with
    | none => exact sum_pos (fun i _ => hL i) univ_nonempty
    | some i => exact hL i
  intro h
  let x (s) : leg L s := ⟨0, hp s⟩
  have h' := (Tensor.ofRaw_eq_zero _).mp h x
  rw [Raw.coeff_ofTable] at h'
  simp [entry, x] at h'

/-- Vandermonde evaluation and interpolation give one rank-one term
for each available output coefficient. -/
theorem polynomial_rank [Infinite K] [Nonempty ι] (L : ι → ℕ) :
    polynomial K L ≤ (∑ i, L i : ℕ) := by
  classical
  let m := ∑ i, L i
  let v (i : Fin m) := Infinite.natEmbedding K i.val
  let M := Matrix.vandermonde v
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr
    (Matrix.det_vandermonde_ne_zero_iff.mpr ((Infinite.natEmbedding K).injective.comp Fin.val_injective))
  let f (l : Fin m) : (s : Option ι) → leg L s → K
    | none, u => M⁻¹ u l
    | some _, u => v l ^ u.val
  let A : Raw K (Option ι) := ⟨leg L, Fin m, f⟩
  have he : polynomial K L = Tensor.ofRaw A := by
    refine Tensor.ofRaw_eq (Raw.equiv_coeff (fun _ => Equiv.refl _) fun x => ?_)
    change (∀ s, leg L s) at x
    refine (Raw.coeff_ofTable _ _ x).trans ?_
    change entry K L x = ∑ l, ∏ s, f l s (x s)
    let b : Fin m := ⟨∑ i, (x (some i)).val,
      sum_lt_sum_of_nonempty univ_nonempty (fun i _ => (x (some i)).isLt)⟩
    simp only [Fintype.prod_option, f, prod_pow_eq_pow_sum]
    let a : Fin m := x none
    change entry K L x = (M⁻¹ * M) a b
    rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_apply]
    change (if b.val = a.val then (1 : K) else 0) = _
    simp only [Fin.ext_iff, eq_comm]
  rw [he]
  have h := Tensor.le_term_count A
  change _ ≤ (Fintype.card (Fin m) : Tensor K (Option ι)) at h
  rwa [Fintype.card_fin] at h

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-! # Three labelled sites with two inputs and one output -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Spectral

abbrev Site := Option Bool

abbrev sides (X Y Z : Type) : Site → Type
  | some false => X
  | some true => Y
  | none => Z

variable {K X Y Z U V W : Type} [Field K]
variable [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]

instance instSides : (s : Site) → Fintype (sides X Y Z s)
  | some false => inferInstanceAs (Fintype X)
  | some true => inferInstanceAs (Fintype Y)
  | none => inferInstanceAs (Fintype Z)

def tuple {L : Site → Type} (x : L (some false)) (y : L (some true)) (z : L none) : ∀ s, L s
  | some false => x
  | some true => y
  | none => z

@[simp] theorem tuple_eta {L : Site → Type} (x : ∀ s, L s) :
    tuple (x (some false)) (x (some true)) (x none) = x := by
  funext s
  rcases s with _ | (_ | _) <;> rfl

def triple (T : X → Y → Z → K) : Raw K Site :=
  Raw.ofTable (sides X Y Z) (fun x => T (x (some false)) (x (some true)) (x none))

def read (A : Raw K Site) (x : A.leg (some false)) (y : A.leg (some true)) (z : A.leg none) :=
  A.coeff (tuple x y z)

theorem prod_site (f : Site → K) : ∏ s, f s = f (some false) * f (some true) * f none := by
  rw [Fintype.prod_option, Fintype.prod_bool]
  ring

theorem read_apply (A : Raw K Site) (x : A.leg (some false)) (y : A.leg (some true)) (z : A.leg none) :
    read A x y z = ∑ i, A.factor i (some false) x * A.factor i (some true) y * A.factor i none z := by
  simp only [read, Raw.coeff, prod_site, tuple]

theorem read_triple (T : X → Y → Z → K) : read (triple T) = T := by
  funext x y z
  exact Raw.coeff_ofTable _ _ _

theorem triple_read (A : Raw K Site) : Tensor.ofRaw (triple (read A)) = Tensor.ofRaw A := by
  let e (s : Site) : (triple (read A)).leg s ≃ A.leg s := match s with
    | none => Equiv.refl _
    | some false => Equiv.refl _
    | some true => Equiv.refl _
  refine Tensor.ofRaw_eq (Raw.equiv_coeff e fun x => ?_)
  refine (Raw.coeff_ofTable _ _ x).trans ?_
  apply congrArg A.coeff
  funext s
  rcases s with _ | (_ | _) <;> rfl

private def coordinates (L : Site → Type) :
    L (some false) × L (some true) × L none ≃ (∀ s, L s) where
  toFun p := tuple p.1 p.2.1 p.2.2
  invFun x := (x (some false), x (some true), x none)
  left_inv _ := rfl
  right_inv _ := tuple_eta _

theorem restricts_triple (A : X → Y → Z → K) (B : U → V → W → K)
    (f : U → X → K) (g : V → Y → K) (h : W → Z → K)
    (he : ∀ u v w, B u v w = ∑ x, ∑ y, ∑ z, f u x * g v y * h w z * A x y z) :
    (triple A).Restricts (triple B) := by
  let L (s : Site) : (triple B).leg s → (triple A).leg s → K := match s with
    | none => h
    | some false => f
    | some true => g
  refine (Raw.restricts_iff _ _).mpr ⟨L, fun x => ?_⟩
  rw [← (coordinates (triple A).leg).sum_comp]
  simp only [Fintype.sum_prod_type, prod_site]
  refine (Raw.coeff_ofTable _ _ x).trans ((he _ _ _).trans ?_)
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  exact congrArg _ (congrFun (congrFun (congrFun (read_triple A).symm i) j) k)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-! # Finite row inequalities for ordered polynomial multiplication -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Spectral

variable (K : Type) [Field K]

def convolution (a b : ℕ) (x : Fin a) (y : Fin b) (z : Fin (a + b - 1)) : K :=
  if x.val + y.val = z.val then 1 else 0

def binary (a b : ℕ) := Tensor.ofRaw (triple (convolution K a b))

def reverseOutput (a b : ℕ) := Tensor.ofRaw (triple (fun x z y => convolution K a b x y z))

/-- The finite determinant and tripling inequalities, in degree indices. -/
def BinaryLaw : Prop :=
  ∀ (f : Tensor K Site →+* NNReal), Monotone f → ∀ p : ℝ, 0 < p →
    (f (Tensor.wire K (some true) none 2) : ℝ) = (2 : ℝ) ^ p → ∀ m : ℕ,
    Row (fun n => (f (binary K (m + 1) (n + 1)) : ℝ) ^ (1 / p))
      (fun n => (f (reverseOutput K (m + 1) (n + 1)) : ℝ) ^ (1 / p)) m

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-! # Keeping the weight-zero coefficients of a nonnegatively graded tensor -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Spectral Finset

variable {K S : Type} [Field K] [Fintype S] [Nonempty S] {X : S → Type} [∀ s, Fintype (X s)]

abbrev array (v : (∀ s, X s) → K) := Tensor.ofRaw (Raw.ofTable X v)

def grade (w : (s : S) → X s → ℤ) (v : (∀ s, X s) → K) (x : ∀ s, X s) : K :=
  if ∑ s, w s (x s) = 0 then v x else 0

private theorem rescale (v : (∀ s, X s) → K) (f : (s : S) → X s → K) :
    array (fun x => (∏ s, f s (x s)) * v x) ≤ array v := by
  classical
  let A := Raw.ofTable X v
  let B := Raw.ofTable X (fun x => (∏ s, f s (x s)) * v x)
  let L (s) (x y : X s) := if y = x then f s x else 0
  refine ⟨L, fun x => ?_⟩
  change (∀ s, X s) at x
  change B.coeff x = ∑ l : A.term, ∏ s, ∑ y : X s, L s (x s) y * A.factor l s y
  simp only [L, ite_mul, zero_mul, Fintype.sum_ite_eq', prod_mul_distrib, ← mul_sum]
  exact (Raw.coeff_ofTable _ _ x).trans (congrArg _ (Raw.coeff_ofTable X v x).symm)

theorem grade_price [Infinite K] [DecidableEq S] (f : Tensor K S →+* NNReal) (hf : Monotone f)
    (v : (∀ s, X s) → K) (w : (s : S) → X s → ℤ)
    (hw : ∀ x, v x ≠ 0 → 0 ≤ ∑ s, w s (x s)) : f (array (grade w v)) ≤ f (array v) := by
  classical
  let P x := Polynomial.X ^ (∑ s, w s (x s)).toNat * Polynomial.C (v x)
  have he : (fun x => (P x).eval 0) = grade w v := by
    funext x
    by_cases hv : v x = 0
    · simp [P, grade, hv]
    by_cases hz : ∑ s, w s (x s) = 0
    · simp [P, grade, hz]
    have hn : (∑ s, w s (x s)).toNat ≠ 0 := by have := hw x hv; omega
    simp [P, grade, hz, hn]
  have h : ZClosure {u | array u ≤ array v} (grade w v) := by
    rw [← he]
    apply Speedup.path_closure P Polynomial.X Polynomial.X_ne_zero
    intro t ht
    rw [Polynomial.eval_X] at ht
    let a s x := t ^ (w s x)
    have ha (x : ∀ s, X s) (l : Finset S) : ∏ s ∈ l, a s (x s) = t ^ (∑ s ∈ l, w s (x s)) := by
      induction l using Finset.induction_on with
      | empty => simp
      | insert i l hi ih => rw [prod_insert hi, sum_insert hi, ih, zpow_add₀ ht]
    have hp : (fun x => (P x).eval t) = fun x => (∏ s, a s (x s)) * v x := by
      funext x
      by_cases hv : v x = 0
      · simp [P, hv]
      simp only [P, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        ha, ← zpow_natCast, Int.toNat_of_nonneg (hw x hv)]
    rw [hp]
    exact rescale v a
  exact NNReal.coe_le_coe.mp (h.price f hf (by positivity) (fun _ ht => NNReal.coe_le_coe.mpr (hf ht)))

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-! Grading away unequal labels exposes a diagonal of identical copies. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Spectral Finset

variable {F ι B : Type} [Field F] [Fintype ι] [Fintype B] [DecidableEq B]
  {X : Option ι → Type} [∀ s, Fintype (X s)]

theorem grade_labels (w : ∀ s, B × X s → ℤ) (v : (∀ s, B × X s) → F) (u : (∀ s, X s) → F)
    (rule : ∀ x, v x ≠ 0 → ((∑ s, w s (x s)) = 0 ↔ ∀ i, (x (some i)).1 = (x none).1))
    (aligned : ∀ x, (∀ i, (x (some i)).1 = (x none).1) → v x = u (fun s => (x s).2)) :
    array (grade w v) = (Fintype.card B : Tensor F (Option ι)) * array u := by
  classical
  rw [← Tensor.diag_eq_natCast B]
  refine Tensor.ofRaw_eq (Raw.equiv_coeff (fun _ => Equiv.refl _) fun x => ?_)
  change (∀ s, B × X s) at x
  erw [Raw.coeff_ofTable, Raw.coeff_mul, Raw.coeff_ofTable]
  have hd : (Raw.diag F (Option ι) B).coeff (fun s => (x s).1) =
      if ∀ i, (x (some i)).1 = (x none).1 then 1 else 0 := by
    change ∑ p, ∏ s, (if (x s).1 = p then (1 : F) else 0) = _
    rw [Fintype.sum_eq_single (x none).1]
    · rw [Fintype.prod_option]
      simp [Fintype.prod_ite_zero]
    · intro p hp
      exact prod_eq_zero (mem_univ none) (ite_eq_right hp.symm)
  change grade w v x = (Raw.diag F (Option ι) B).coeff (fun s => (x s).1) * u (fun s => (x s).2)
  rw [hd, grade]
  by_cases h : ∀ i, (x (some i)).1 = (x none).1
  · rw [ite_eq_left h, one_mul, ← aligned x h]
    by_cases hv : v x = 0
    · simp [hv]
    · rw [ite_eq_left ((rule x hv).mpr h)]
  · rw [ite_eq_right h, zero_mul]
    by_cases hv : v x = 0
    · simp [hv]
    · rw [ite_eq_right (mt (rule x hv).mp h)]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-!
# Equal-block degeneration

For block number `a`, length `l` and offset `d`, assign the input the
integer weight `a(a-1)l + a(2d+1)`. Its excess above the supporting
line for the output block `b` is positive unless `a=b`. The supporting
lines add to the output weight because degrees add.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Finset Spectral

variable {ι : Type} [Fintype ι]

def weight (a l d m : ℤ) := a * (a - 1) * l + a * (2 * d + m)

private theorem excess (a b l d : ℤ) (hd : 0 ≤ d) (hl : d < l) (hne : a ≠ b) :
    0 < (a - b) * ((a - b - 1) * l + 2 * d + 1) := by
  rcases lt_or_gt_of_ne hne with h | h
  · have ht := mul_le_mul_of_nonneg_right (show a - b - 1 ≤ -2 by omega) (show 0 ≤ l by omega)
    exact mul_pos_of_neg_of_neg (by omega) (by omega)
  · have ht := mul_nonneg (show 0 ≤ a - b - 1 by omega) (show 0 ≤ l by omega)
    exact mul_pos (by omega) (by omega)

theorem weights (a l d : ι → ℤ) (b u : ℤ)
    (hd : ∀ i, 0 ≤ d i) (hl : ∀ i, d i < l i) (he : ∑ i, (a i * l i + d i) = b * (∑ i, l i) + u) :
    let W := -weight b (∑ i, l i) u (Fintype.card ι) + ∑ i, weight (a i) (l i) (d i) 1
    0 ≤ W ∧ (W = 0 ↔ ∀ i, a i = b) := by
  let v i := (a i - b) * ((a i - b - 1) * l i + 2 * d i + 1)
  have hv i : 0 ≤ v i ∧ (v i = 0 ↔ a i = b) := by
    by_cases h : a i = b
    · simp [v, h]
    · have hp : 0 < v i := excess _ _ _ _ (hd i) (hl i) h
      exact ⟨hp.le, iff_of_false hp.ne' h⟩
  have he' i : weight (a i) (l i) (d i) 1 =
      v i + (2 * b) * (a i * l i + d i) - b * (b + 1) * l i + b := by unfold v weight; ring
  have hW : -weight b (∑ i, l i) u (Fintype.card ι) + ∑ i, weight (a i) (l i) (d i) 1 =
      ∑ i, v i := by
    simp_rw [he']
    rw [sum_add_distrib, sum_sub_distrib, sum_add_distrib, ← mul_sum, he, ← mul_sum, sum_const]
    simp only [weight, card_univ, nsmul_eq_mul]
    ring
  dsimp only
  rw [hW]
  refine ⟨sum_nonneg (fun i _ => (hv i).1), ?_⟩
  simp only [sum_eq_zero_iff_of_nonneg (fun i _ => (hv i).1), mem_univ, forall_true_left, (hv _).2]

variable (K : Type) [Field K] (L : ι → ℕ) (k : ℕ)

private abbrev block (s : Option ι) := Fin k × leg L s

private def join (s : Option ι) (p : block L k s) : leg (fun i => k * L i) s :=
  Fin.cast (by cases s <;> simp [length, mul_sum]) (finProdFinEquiv p)

private theorem join_val (s : Option ι) (p : block L k s) :
    (join L k s p).val = p.1.val * length L s + p.2.val := by
  simp [join, finProdFinEquiv, add_comm, mul_comm]

private def big (x : ∀ s, block L k s) := entry K (fun i => k * L i) (fun s => join L k s (x s))

private def grading (s : Option ι) (p : block L k s) : ℤ :=
  if s.isNone then -weight p.1.val (length L s) p.2.val (Fintype.card ι)
  else weight p.1.val (length L s) p.2.val 1

private theorem grading_rule (x : ∀ s, block L k s) (hx : big K L k x ≠ 0) :
    0 ≤ ∑ s, grading L k s (x s) ∧
      ((∑ s, grading L k s (x s)) = 0 ↔ ∀ i, (x (some i)).1 = (x none).1) := by
  have he : ∑ i, ((x (some i)).1.val * L i + (x (some i)).2.val) =
      (x none).1.val * (∑ i, L i) + (x none).2.val := by
    simpa [big, entry, join_val, length] using hx
  have hw := weights (fun i => ((x (some i)).1.val : ℤ)) (fun i => (L i : ℤ))
    (fun i => ((x (some i)).2.val : ℤ)) (x none).1.val (x none).2.val
    (fun _ => by positivity) (fun i => by exact_mod_cast (x (some i)).2.isLt) (by exact_mod_cast he)
  simpa [Fintype.sum_option, grading, length, Fin.ext_iff] using hw

private theorem table_blocks :
    array (grade (grading L k) (big K L k)) = (k : Tensor K (Option ι)) * polynomial K L := by
  have he := grade_labels (grading L k) (big K L k) (entry K L)
    (fun x hx => (grading_rule K L k x hx).2) (by
      intro x h
      simp only [big, entry, join_val, length, h, sum_add_distrib, ← mul_sum, add_right_inj])
  rw [Fintype.card_fin] at he
  exact he

theorem polynomial_dilate [Infinite K] [DecidableEq ι] (f : Tensor K (Option ι) →+* NNReal)
    (hf : Monotone f) : k * f (polynomial K L) ≤ f (polynomial K (fun i => k * L i)) := by
  have hb : array (big K L k) ≤ polynomial K (fun i => k * L i) := by
    refine Raw.Restricts.pullback (join L k) fun x => ?_
    change (∀ s, block L k s) at x
    refine (Raw.coeff_ofTable _ _ x).trans ?_
    exact (Raw.coeff_ofTable _ (entry K (fun i => k * L i)) (fun s => join L k s (x s))).symm
  have h := grade_price f hf (big K L k) (grading L k) (fun x hx => (grading_rule K L k x hx).1)
  rw [table_blocks, map_mul, map_natCast] at h
  exact h.trans (hf hb)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-! # Continuum profile for univariate polynomial multiplication -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Spectral Filter
open scoped Topology

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Field K] [Infinite K]

theorem scaling_polynomial (f : Tensor K (Option ι) →+* NNReal) (hf : Monotone f) :
    Scaling (fun L => (f (polynomial K L) : ℝ)) := by
  refine ⟨fun _ => by positivity, fun _ _ h => NNReal.coe_le_coe.mpr (hf (polynomial_mono K h)), ?_, ?_⟩
  · intro L
    have h := hf (polynomial_rank K L)
    rw [map_natCast] at h
    exact_mod_cast h
  · intro k L
    exact_mod_cast polynomial_dilate K L k f hf

def profile (f : Tensor K (Option ι) →+* NNReal) (t : ι → ℝ) :=
  scale (fun L => (f (polynomial K L) : ℝ)) t

variable {f : Tensor K (Option ι) →+* NNReal} (hf : Monotone f) {t : ι → ℝ} (ht : ∀ i, 0 < t i)
include hf ht

theorem profile_pos : 0 < profile f t := by
  apply (scaling_polynomial f hf).scale_pos ht (L := fun _ => 1)
  have h := hf (Tensor.one_le _ (polynomial_ne_zero K (L := fun _ => 1) (fun _ => zero_lt_one)))
  rw [map_one] at h
  exact_mod_cast zero_lt_one.trans_le h

theorem log_profile_limit {α : Type*} {l : Filter α} {N : α → ℝ}
    (hN : Tendsto N l atTop) {L : α → ι → ℕ}
    (hL : ∀ i, Tendsto (fun n => (L n i : ℝ) / N n) l (𝓝 (t i))) :
    Tendsto (fun n => Real.log (f (polynomial K (L n))) - Real.log (N n))
      l (𝓝 (Real.log (profile f t))) := by
  have h := (scaling_polynomial f hf).limit ht hN hL
  have hp := profile_pos hf ht
  apply (h.log hp.ne').congr'
  filter_upwards [hN.eventually_gt_atTop 0, h.eventually_const_lt hp] with n hn hn'
  exact Real.log_div ((div_pos_iff_of_pos_right hn).mp hn').ne' hn.ne'

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-! # From ordinary base-two prices to natural-log profiles -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Spectral

def two {α : Type*} (x y : α) : Bool → α
  | false => x
  | true => y

def pairSite (i j : Fin 3) : Site → Fin 3
  | none => -i - j
  | some false => i
  | some true => j

def placement {X : Type*} (v : Fin 3 → X) (i j : Fin 3) := v ∘ pairSite i j

theorem pairSite_bijective {i j : Fin 3} (hij : i ≠ j) : Function.Bijective (pairSite i j) := by
  fin_cases i <;> fin_cases j <;> first | contradiction | decide

variable {K S : Type} [Field K] [Fintype S] [Nontrivial S] [DecidableEq S]
    {X : Type*} [PseudoMetricSpace X] (A : MatrixExponent.Prices.Atlas K X) (v : S → X)

private theorem exists_point :
    ∃ f : Tensor K S →+* NNReal, Monotone f ∧
      ∀ B, Real.log 2 * A.price v B = A.price v 2 * Real.log (f B) := by
  obtain ⟨_, d, _, f, hf, he⟩ := A.valid v
  have hn (B : Tensor K S) : 0 ≤ f B := by simpa using hf (Tensor.zero_le B)
  let g : Tensor K S →+* NNReal :=
    { toFun := fun B => ⟨f B, hn B⟩
      map_zero' := Subtype.ext (map_zero f)
      map_one' := Subtype.ext (map_one f)
      map_add' := fun a b => Subtype.ext (f.map_add a b)
      map_mul' := fun a b => Subtype.ext (f.map_mul a b) }
  refine ⟨g, hf, fun B => ?_⟩
  change Real.log 2 * A.price v B = A.price v 2 * Real.log (f B)
  rw [he, Tensor.values, Tensor.values, map_ofNat]
  ring

def point : Tensor K S →+* NNReal := (exists_point A v).choose

theorem point_mono : Monotone (point A v) := (exists_point A v).choose_spec.1

theorem price_eq (B : Tensor K S) :
    Real.log 2 * A.price v B = A.price v 2 * Real.log (point A v B) :=
  (exists_point A v).choose_spec.2 B

theorem placement_two (v : Fin 3 → X) {i j : Fin 3} (hij : i ≠ j) :
    A.price (placement v i j) 2 = A.price v 2 := by
  unfold placement
  rw [A.place, Function.comp_apply, Tensor.place_eq_group _ (pairSite_bijective hij).2, map_ofNat]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-! # Reindexing the two-input polynomial tensor -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Spectral

variable {K X Y Z : Type} [Field K] [Fintype X] [Fintype Y] [Fintype Z]

def flip : Site → Site
  | none => none
  | some false => some true
  | some true => some false

def turn : Site → Site
  | none => some true
  | some false => some false
  | some true => none

private theorem turn_le (T : X → Y → Z → K) :
    Tensor.place turn (Tensor.ofRaw (triple T)) ≤ Tensor.ofRaw (triple (fun x z y => T x y z)) := by
  let A := (triple T).group turn
  let L (s : Site) : A.leg s → sides X Z Y s := match s with
    | none => fun x => x ⟨some true, rfl⟩
    | some false => fun x => x ⟨some false, rfl⟩
    | some true => fun x => x ⟨none, rfl⟩
  refine Raw.Restricts.pullback L fun x => ?_
  erw [Raw.coeff_group, Raw.coeff_ofTable, Raw.coeff_ofTable]
  rfl

theorem place_turn (a b : ℕ) : Tensor.place turn (binary K a b) = reverseOutput K a b := by
  apply le_antisymm (turn_le _)
  have h := Tensor.place_mono turn (turn_le (fun x z y => convolution K a b x y z))
  rw [← Tensor.place_comp, show turn ∘ turn = id by funext s; rcases s with _ | (_ | _) <;> rfl,
    Tensor.place_id] at h
  exact h

private theorem flip_le (a b : ℕ) : Tensor.place flip (binary K a b) ≤ binary K b a := by
  let A := (triple (convolution K a b)).group flip
  let L (s : Site) : A.leg s → sides (Fin b) (Fin a) (Fin (b + a - 1)) s := match s with
    | none => fun x => Fin.cast (show a + b - 1 = b + a - 1 by omega) (x ⟨none, rfl⟩)
    | some false => fun x => x ⟨some true, rfl⟩
    | some true => fun x => x ⟨some false, rfl⟩
  refine Raw.Restricts.pullback L fun x => ?_
  erw [Raw.coeff_group, Raw.coeff_ofTable, Raw.coeff_ofTable]
  unfold convolution
  rw [Nat.add_comm]
  rfl

theorem place_flip (a b : ℕ) : Tensor.place flip (binary K a b) = binary K b a := by
  apply le_antisymm (flip_le _ _)
  have h := Tensor.place_mono flip (flip_le (K := K) b a)
  rw [← Tensor.place_comp, show flip ∘ flip = id by funext s; rcases s with _ | (_ | _) <;> rfl,
    Tensor.place_id] at h
  exact h

theorem binary_eq (a b : ℕ) : binary K a b = polynomial K (two a b) := by
  classical
  let d := length (two a b) none
  have hd : d = a + b := by simp [d, length, two, add_comm]
  let W (x : Fin a) (y : Fin b) (z : Fin d) : K := if x.val + y.val = z.val then 1 else 0
  let A := Raw.ofTable (leg (two a b)) (entry K (two a b))
  have he : read A = W := by
    funext x y z
    refine (Raw.coeff_ofTable _ _ _).trans ?_
    simp [entry, W, tuple, Nat.add_comm]
  change Tensor.ofRaw (triple _) = Tensor.ofRaw A
  rw [← triple_read A, he]
  change Tensor.ofRaw (triple (convolution K a b)) = Tensor.ofRaw (triple W)
  let e := Fin.castLE (show a + b - 1 ≤ d by omega)
  let δ {α : Type} (x y : α) : K := if x = y then 1 else 0
  apply Tensor.ofRaw_eq
  constructor
  · refine restricts_triple _ _ δ δ (fun z z' => δ z (e z')) fun x y z => ?_
    simp only [δ, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Fintype.sum_ite_eq]
    let l : Fin (a + b - 1) := ⟨x.val + y.val, by have := x.isLt; have := y.isLt; omega⟩
    rw [Fintype.sum_eq_single l]
    · simp [convolution, l, W, e, Fin.ext_iff, eq_comm]
    · intro j hj
      have h' : x.val + y.val ≠ j.val := fun h' => hj (Fin.ext h'.symm)
      simp [convolution, h']
  · refine restricts_triple _ _ δ δ (fun z z' => δ (e z) z') fun x y z => ?_
    simp only [δ, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Fintype.sum_ite_eq]
    rfl

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-! # Width profiles on a three-point placement -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Filter
open scoped Topology

variable {K : Type} [Field K] {X : Type*} [PseudoMetricSpace X] (A : MatrixExponent.Prices.Atlas K X)
    (v : Fin 3 → X)

def pairs (i j : Fin 3) (x y : ℝ) : ℝ :=
  if i ≠ j ∧ 0 < x ∧ 0 < y then
    A.price v 2 * Real.log (profile (point A (placement v i j)) (two x y))
  else 0

variable [Infinite K] {i j : Fin 3} {x y : ℝ}

theorem pairs_limit (hij : i ≠ j) (hx : 0 < x) (hy : 0 < y)
    {α : Type*} {l : Filter α} {N : α → ℝ} (hN : Tendsto N l atTop) {L : α → Bool → ℕ}
    (hL : ∀ i, Tendsto (fun n => (L n i : ℝ) / N n) l (𝓝 (two x y i))) :
    Tendsto (fun n => Real.log 2 * A.price (placement v i j) (polynomial K (L n)) -
      A.price v 2 * Real.log (N n)) l (𝓝 (pairs A v i j x y)) := by
  have ht : ∀ b, 0 < two x y b := by rintro (_ | _) <;> assumption
  have h := (log_profile_limit (point_mono A (placement v i j)) ht hN hL).const_mul (A.price v 2)
  rw [pairs, ite_eq_left ⟨hij, hx, hy⟩]
  apply h.congr'
  filter_upwards [] with n
  rw [price_eq A (placement v i j), placement_two A v hij, mul_sub]

theorem pairs_scale (hij : i ≠ j) {s : ℝ} (hs : 0 < s) (hx : 0 < x) (hy : 0 < y) :
    pairs A v i j (s * x) (s * y) = pairs A v i j x y + A.price v 2 * Real.log s := by
  have ht : ∀ b, 0 < two x y b := by rintro (_ | _) <;> assumption
  let f := point A (placement v i j)
  have hf : Monotone f := point_mono _ _
  have he : profile f (two (s * x) (s * y)) = s * profile f (two x y) := by
    rw [show two (s * x) (s * y) = s • two x y by funext b; cases b <;> rfl]
    exact (scaling_polynomial f hf).scale_smul ht hs
  rw [pairs, pairs, ite_eq_left ⟨hij, mul_pos hs hx, mul_pos hs hy⟩, ite_eq_left ⟨hij, hx, hy⟩,
    he, Real.log_mul hs.ne' (profile_pos hf ht).ne']
  ring

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-! Restrictions by absorbing the last input at the output site or extracting a fixed total degree. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Spectral Finset

variable {K : Type} [Field K]

private theorem placed_le {S T U : Type} [Fintype S] [Fintype T] [Fintype U]
    [DecidableEq S] [DecidableEq T] [DecidableEq U] {L : S → ℕ} {M : T → ℕ}
    (f : Option S → U) (g : Option T → U)
    (v : ∀ t, (∀ s, f s = g t → leg L s) → leg M t)
    (he : ∀ x, entry K L x = entry K M (fun t => v t (fun s _ => x s))) :
    Tensor.place f (polynomial K L) ≤ Tensor.place g (polynomial K M) := by
  let A := Raw.ofTable (leg L) (entry K L)
  let B := Raw.ofTable (leg M) (entry K M)
  let V (u : U) (x : (A.group f).leg u) : (B.group g).leg u :=
    fun t => v t (fun s h => x ⟨s, h.trans t.property⟩)
  refine Raw.Restricts.pullback V fun x => ?_
  erw [Raw.coeff_group, Raw.coeff_group, Raw.coeff_ofTable, Raw.coeff_ofTable, he]
  congr 1
  funext t
  unfold V
  congr 1
  funext s h
  have aux (u : U) (h : f s = u) : x (f s) ⟨s, rfl⟩ = x u ⟨s, h⟩ := by cases h; rfl
  exact aux _ h

private def pins (i j k : Fin 3) : Site → Fin 3
  | none => k
  | some false => i
  | some true => j

def terminal (k : Fin 3) : Option (Fin 3) → Fin 3
  | none => k
  | some i => i

variable {i j k : Fin 3} {L : Fin 3 → ℕ}

private theorem pairSite_eq (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    pairSite i j = pins i j k := by
  funext t
  rcases t with _ | (_ | _) <;> simp [pairSite, pins]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> first | contradiction | decide

private theorem sum_three (v : Fin 3 → ℕ) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ t, v t = v i + v j + v k := by
  have he : {i, j, k} = (univ : Finset (Fin 3)) := by
    apply Finset.eq_univ_of_card
    simp [hij, hik, hjk]
  simp [← he, hij, hik, hjk, add_assoc]

private theorem pair_length (a b : ℕ) : length (two a b) none = a + b := by
  simp [length, two, add_comm]

/-- An out-of-range difference uses the spare output coordinate of the pair. -/
private def shift (d z w : ℕ) : ℕ :=
  if w ≤ z ∧ z - w < d then z - w else d - 1

theorem absorb (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : 0 < L i) :
    Tensor.place (terminal k) (polynomial K L) ≤
      Tensor.place (pairSite i j) (polynomial K (two (L i) (L j))) := by
  rw [pairSite_eq hij hik hjk]
  let M := two (L i) (L j)
  let D := L i + L j
  have hd : length M none = D := pair_length _ _
  have hshift (z w : ℕ) : shift D z w < length M none := by
    rw [hd]
    unfold shift D
    split <;> omega
  let v : ∀ t, (∀ s, terminal k s = pins i j k t → leg L s) → leg M t
    | some false, x => x (some i) rfl
    | some true, x => x (some j) rfl
    | none, x => ⟨shift D (x none rfl).val (x (some k) rfl).val, hshift _ _⟩
  refine placed_le _ _ v fun x => ?_
  have h₁ : (x (some i)).val < L i := (x (some i)).isLt
  have h₂ : (x (some j)).val < L j := (x (some j)).isLt
  simp only [entry, sum_three _ hij hik hjk, Fintype.sum_bool, v]
  congr 1
  apply propext
  unfold shift D
  split <;> omega

/-- Pin the output at degree `L i + L j - 1` and reverse the degree
on input `k` to expose a two-input polynomial with output at `k`. -/
theorem extract_pair (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : 0 < L i)
    (hk : L i + L j ≤ L k) :
    Tensor.place (some ∘ pairSite i j) (polynomial K (two (L i) (L j))) ≤ polynomial K L := by
  rw [pairSite_eq hij hik hjk]
  let M := two (L i) (L j)
  let D := L i + L j
  have hd : length M none = D := pair_length _ _
  have hout : D - 1 < length L none := by
    rw [length, sum_three _ hij hik hjk]
    unfold D
    omega
  let v : ∀ t, (∀ s, some (pins i j k s) = t → leg M s) → leg L t
    | none, _ => ⟨D - 1, hout⟩
    | some l, x =>
      if hi' : i = l then Fin.cast (congrArg L hi') (x (some false) (congrArg some hi'))
      else if hj' : j = l then Fin.cast (congrArg L hj') (x (some true) (congrArg some hj'))
      else
        have eq : k = l := by omega
        have hD : D - 1 < L l := by rw [← eq]; unfold D; omega
        ⟨D - 1 - (x none (congrArg some eq)).val, (Nat.sub_le _ _).trans_lt hD⟩
  rw [← Tensor.place_id (polynomial K L)]
  refine placed_le _ _ v fun x => ?_
  have h₁ : (x none).val < D := hd ▸ (x none).isLt
  simp only [entry, sum_three _ hij hik hjk, Fintype.sum_bool, v, hij, hik, hjk,
    dite_eq_right, dite_eq_left, eq_self, not_false_eq_true]
  congr 1
  apply propext
  change (x (some true)).val + (x (some false)).val = (x none).val ↔
    (x (some false)).val + (x (some true)).val + (D - 1 - (x none).val) = D - 1
  omega

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-! # Compatibility of the width profiles with site permutations -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Filter Spectral
open scoped Topology

variable {K : Type} [Field K] {X : Type*} [PseudoMetricSpace X] (A : MatrixExponent.Prices.Atlas K X)
    (v : Fin 3 → X) {i j k : Fin 3} {x y : ℝ}

theorem remaining (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : -i - j = k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> first | contradiction | decide

theorem price_flip (i j : Fin 3) (a b : ℕ) :
    A.price (placement v i j) (binary K a b) = A.price (placement v j i) (binary K b a) := by
  have he : placement v i j = placement v j i ∘ flip := by
    funext s
    rcases s with _ | (_ | _) <;> simp [placement, pairSite, flip, sub_eq_add_neg, add_comm]
  rw [he, A.place, Function.comp_apply, place_flip]

theorem price_turn (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a b : ℕ) :
    A.price (placement v i k) (binary K a b) = A.price (placement v i j) (reverseOutput K a b) := by
  have he : placement v i k = placement v i j ∘ turn := by
    funext s
    rcases s with _ | (_ | _) <;>
      simp [placement, pairSite, turn, remaining hij hik hjk, remaining hik hij hjk.symm]
  rw [he, A.place, Function.comp_apply, place_turn]

theorem binary_ne_zero (a b : ℕ) : binary K (a + 1) (b + 1) ≠ 0 := by
  rw [binary_eq]
  exact polynomial_ne_zero K (by rintro (_|_) <;> exact Nat.succ_pos _)

theorem reverse_ne_zero (a b : ℕ) : reverseOutput K (a + 1) (b + 1) ≠ 0 := by
  rw [← place_turn]
  intro hz
  have he := congrArg (Tensor.place turn) hz
  rw [← Tensor.place_comp, show turn ∘ turn = id by funext s; rcases s with _ | (_ | _) <;> rfl,
    Tensor.place_id, Tensor.place_zero] at he
  exact binary_ne_zero a b he

theorem point_pos {f : Tensor K Site →+* NNReal} (hf : Monotone f)
    {T : Tensor K Site} (hT : T ≠ 0) : 0 < (f T : ℝ) := by
  have h := hf (Tensor.one_le _ hT)
  rw [map_one] at h
  exact_mod_cast zero_lt_one.trans_le h

theorem scaled_wire (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {d : ℝ} (hd : 0 < d) (he : Dist.dist (v j) (v k) = d) :
    0 < A.price v 2 ∧
      (point A (placement v i j) (Tensor.wire K (some true) none 2) : ℝ) = (2 : ℝ) ^ (d / A.price v 2) := by
  let w := placement v i j
  let B := Tensor.wire K (some true) none 2
  have he' : A.price w B = d := by
    rw [show A.price w B = Dist.dist (w (some true)) (w none) from A.wire _ _ _]
    simpa [w, placement, pairSite, remaining hij hik hjk] using he
  have hD := price_eq A w B
  rw [he', placement_two A v hij] at hD
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hone : (1 : ℝ) ≤ point A w B := by
    have h := point_mono A w (Tensor.one_le_wire K (some true) none (n := 2) (by decide))
    rw [map_one] at h
    exact_mod_cast h
  have hpos : 0 < A.price v 2 := pos_of_mul_pos_left (hD ▸ mul_pos hlog hd) (Real.log_nonneg hone)
  refine ⟨hpos, ?_⟩
  rw [Real.rpow_def_of_pos (by norm_num), ← mul_div_assoc, hD, mul_div_cancel_left₀ _ hpos.ne',
    Real.exp_log (zero_lt_one.trans_le hone)]

variable [Infinite K]

theorem binary_limit (hij : i ≠ j) (hx : 0 < x) (hy : 0 < y) {a b : ℝ → ℕ}
    (ha : Tendsto (fun n => (a n : ℝ) / n) atTop (𝓝 x))
    (hb : Tendsto (fun n => (b n : ℝ) / n) atTop (𝓝 y)) :
    Tendsto (fun n => Real.log 2 * A.price (placement v i j) (binary K (a n + 1) (b n + 1)) -
      A.price v 2 * Real.log n) atTop (𝓝 (pairs A v i j x y)) := by
  have h₁ : Tendsto (fun n : ℝ => 1 / n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  simp_rw [binary_eq]
  apply pairs_limit A v hij hx hy tendsto_id
  rintro (_ | _)
  · simpa only [two, Nat.cast_add, Nat.cast_one, add_div, add_zero, id_eq] using ha.add h₁
  · simpa only [two, Nat.cast_add, Nat.cast_one, add_div, add_zero, id_eq] using hb.add h₁

theorem pairs_symm (i j : Fin 3) (x y : ℝ) : pairs A v i j x y = pairs A v j i y x := by
  by_cases h : i ≠ j ∧ 0 < x ∧ 0 < y
  swap; · have : ¬(j ≠ i ∧ 0 < y ∧ 0 < x) := by tauto
          simp only [pairs, ite_eq_right h, ite_eq_right this]
  obtain ⟨hij, hx, hy⟩ := h
  have ha := tendsto_nat_floor_mul_div_atTop hx.le
  have hb := tendsto_nat_floor_mul_div_atTop hy.le
  have h := binary_limit A v hij hx hy ha hb
  simp_rw [price_flip A v i j] at h
  exact tendsto_nhds_unique h (binary_limit A v hij.symm hy hx hb ha)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end
