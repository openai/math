import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Gaps
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Model
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import OAI.LinearAlgebra.MatrixExponent.BlockProducts
import Mathlib.LinearAlgebra.Vandermonde
import OAI.LinearAlgebra.MatrixExponent.CircuitCost
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Possible
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.TreePossible
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Dual
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Bounds
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Border.Surplus

/-!
# Finite support from a Shannon entropy bound

Keep every atom of weight at least `exp (-L)`. No zero-weight atom
contributes, and the discarded mass times `L` is bounded by the entropy.
Both entropy and the scale logarithm are taken in natural units.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

open Filter Finset
open scoped Classical
variable {ι X : Type*} {w : ι → ℝ} {E : ℝ}

theorem entropy_mass (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1)
    (he : HasSum (fun i => -w i * Real.log (w i)) E) (L : ℝ) :
    ∃ S : Finset ι, (∀ i ∈ S, 0 < w i) ∧ (S.card : ℝ) ≤ Real.exp L ∧
      (1 - ∑ i ∈ S, w i) * L ≤ E := by
  have hf := hs.summable.tendsto_cofinite_zero.eventually_lt_const (Real.exp_pos (-L))
  let S := (eventually_cofinite.mp hf).toFinset
  have hS (i) : i ∈ S ↔ Real.exp (-L) ≤ w i := by simp [S]
  have hm (T : Finset ι) : ∑ i ∈ T, w i ≤ 1 := sum_le_hasSum T (fun i _ => hw i) hs
  refine ⟨S, fun i hi => (Real.exp_pos _).trans_le ((hS i).mp hi), ?_, ?_⟩
  · have ht : ∑ _ ∈ S, Real.exp (-L) ≤ (1 : ℝ) :=
      (sum_le_sum (fun i hi => (hS i).mp hi)).trans (hm S)
    rw [sum_const, nsmul_eq_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos L)] at ht
    exact ht
  · have hr : HasSum (fun i => if i ∈ S then w i else 0) (∑ i ∈ S, w i) := by
      convert hasSum_sum_of_ne_finset_zero (L := .unconditional ι) (s := S) (f := fun i => if i ∈ S then w i else 0)
        (fun i hi => ite_eq_right hi) using 1
      simp
    apply hasSum_le _ ((hs.sub hr).mul_right L) he
    intro i
    by_cases hi : i ∈ S
    · rw [ite_eq_left hi, sub_self, zero_mul]
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (hw i))
        (Real.log_nonpos (hw i) (by simpa using hm {i}))
    · rw [ite_eq_right hi, sub_zero]
      rcases (hw i).eq_or_lt with hz | hp
      · simp [← hz]
      · have hh := Real.log_le_log hp (le_of_not_ge (mt (hS i).mpr hi))
        rw [Real.log_exp] at hh
        nlinarith only [hh, hp]

/-- A positive gap remains at support rate `3*η+ε`. This includes
entropy rate zero without requiring that the seed be deterministic. -/
theorem entropy_gap {accept : ι → X → Prop} {good : X → Prop} {n : ℕ} {η ε : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (ha : Accurate w accept good)
    (he : HasSum (fun i => -w i * Real.log (w i)) E) (hn : 2 ≤ n) (hη : 0 ≤ η)
    (hε : 0 < ε) (hb : E ≤ (η + ε / 4) * Real.log n) :
    ∃ S : Finset ι, S.Nonempty ∧ (S.card : ℝ) ≤ (n : ℝ) ^ (3 * η + ε) ∧ Gap w accept good S := by
  have hn' : 1 < (n : ℝ) := by exact_mod_cast hn
  have hl := Real.log_pos hn'
  obtain ⟨S, _, hc, hm⟩ := entropy_mass hw hs he (Real.log n * (3 * η + ε))
  have hmass : 2 / 3 < ∑ i ∈ S, w i := by
    by_contra! h
    have hx := mul_le_mul_of_nonneg_right (by linarith : 1 / 3 ≤ 1 - ∑ i ∈ S, w i)
      (by positivity : 0 ≤ Real.log n * (3 * η + ε))
    nlinarith only [hb, hm, hx, mul_pos hl hε]
  refine ⟨S, ?_, ?_, mass_gap hw hs ha S hmass⟩
  · exact nonempty_of_ne_empty (by rintro rfl; norm_num at hmass)
  · rwa [Real.rpow_def_of_pos (by linarith)]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-! A mixture of a uniform verifier and two constant decisions. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open Filter Finset
open scoped Classical
variable {F : Type*} [Field F] {n : ℕ}

private def constant (n : ℕ) (a : F) : Test F n :=
  ⟨1, fun _ => MvPolynomial.C a, fun _ => MvPolynomial.C 0⟩

private theorem const_accept (x : Index n → F) (a : F) :
    (constant n a).accept x ↔ a = 0 := by simp [Test.accept, constant]

private theorem const_cost (a : F) {c : ℝ} (h : 1 ≤ c) : (constant n a).cost c :=
  ⟨0, _, .nil, fun _ => ⟨.inl ⟨_, rfl⟩, .inl ⟨_, rfl⟩⟩, by simpa [constant] using h⟩

private def overhead (q : ℝ) :=
  -((2 / 3 - q) * Real.log (2 / 3 - q) + (1 / 3) * Real.log (1 / 3) + q * Real.log q)

private theorem mix {s c p q : ℝ} (h : Uniform F n s c p) (hc : 1 ≤ c)
    (hq : 0 < q) (hq' : q ≤ 2 / 3) (hg : 1 / 3 ≤ q - p * q) :
    ∃ (L : ℕ) (A : Fin L → Test F n) (w : Fin L → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ -(∑ i, w i * Real.log (w i)) ≤ overhead q + q * Real.log s ∧
      (∀ i, (A i).cost c) ∧
      ∀ x, (∑ i, if (A i).accept x ↔ Correct x then w i else 0) ≥ 2 / 3 := by
  obtain ⟨L, T, hL, hLs, hcost, on, off⟩ := h
  let A : Fin (L + 1 + 1) → Test F n := Fin.cons (constant n 0) (Fin.cons (constant n 1) T)
  let u := q / (L : ℝ)
  let w : Fin (L + 1 + 1) → ℝ := Fin.cons (2 / 3 - q) (Fin.cons (1 / 3) (fun _ => u))
  have pos : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hu : 0 ≤ u := (div_pos hq pos).le
  have hu' : (L : ℝ) * u = q := mul_div_cancel₀ q pos.ne'
  have mass : (∑ _ : Fin L, u) = q := by simp [hu']
  refine ⟨_, A, w, ?_, ?_, ?_, ?_, ?_⟩
  · exact Fin.cases (sub_nonneg.mpr hq') (Fin.cases (by norm_num [w]) (fun _ => hu))
  · simp only [w, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mass]
    ring
  · simp only [w, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← Finset.sum_mul, mass]
    rw [show Real.log u = Real.log q - Real.log L from Real.log_div hq.ne' pos.ne']
    unfold overhead
    linarith [mul_le_mul_of_nonneg_left (Real.log_le_log pos hLs) hq.le]
  · exact Fin.cases (const_cost 0 hc) (Fin.cases (const_cost 1 hc) hcost)
  · intro x
    simp only [A, w, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, const_accept, one_ne_zero]
    by_cases hx : Correct x
    · simp only [hx, on x hx, iff_true, ite_true, ite_false, mass]
      linarith
    · have loss : (∑ i, if (T i).accept x then u else 0) ≤ p * q := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        simpa only [mul_assoc, hu'] using mul_le_mul_of_nonneg_right (off x hx) hu
      have both : (∑ i, if ¬ (T i).accept x then u else 0) +
          (∑ i, if (T i).accept x then u else 0) = q := by
        rw [← mass, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : (T i).accept x <;> simp [hi]
      simp only [hx, iff_false, not_true_eq_false, ite_false, ite_true]
      linarith

/-- Pay for the original seed with probability just above the required
acceptance gap. Its error is chosen small enough to preserve that gap. -/
theorem Support.entropy {ρ v η : ℝ} (h : Support F ρ v) (hρ : 0 ≤ ρ) (hv : 0 ≤ v)
    (hη : ρ / 3 ≤ η) : Entropy F η v := by
  intro ε hε
  let p := min (1 / 6 : ℝ) (ε / (4 * (ρ + 1)))
  have hp : 0 < p := by dsimp [p]; positivity
  have hp' : p ≤ 1 / 6 := min_le_left ..
  have hpρ : p * (4 * (ρ + 1)) ≤ ε := (le_div_iff₀ (by positivity)).mp (min_le_right ..)
  let q := 1 / 3 + p
  have hq : 0 < q := by dsimp [q]; linarith
  have hq' : q ≤ 1 / 2 := by dsimp [q]; linarith
  have hg : 1 / 3 ≤ q - p * q := by
    have := mul_le_mul_of_nonneg_left hq' hp.le
    dsimp [q] at this ⊢
    linarith
  have hrate : q * (ρ + ε) ≤ η + 3 * ε / 4 := by
    have := mul_le_mul_of_nonneg_right hq' hε.le
    dsimp [q] at this ⊢
    linarith
  have grow := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [h ε hε p hp, eventually_ge_atTop 1, grow.eventually_ge_atTop (overhead q / (ε / 4))]
    with n hs hn he
  have hn' : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
  obtain ⟨L, A, w, h₀, h₁, h₂, h₃, h₄⟩ := mix hs (Real.one_le_rpow hn' (by linarith)) hq (by linarith) hg
  refine ⟨L, A, w, h₀, h₁, h₂.trans ?_, h₃, h₄⟩
  have hc : overhead q ≤ Real.log n * (ε / 4) := (div_le_iff₀ (by positivity)).mp he
  rw [Real.log_rpow (by positivity)]
  linarith [mul_le_mul_of_nonneg_right hrate (Real.log_nonneg hn')]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-! # A polynomial encoding of all output blocks -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open Finset
open scoped Classical

variable {A : Type*} [CommRing A] {n U R : ℕ}

def pad (f : Fin n → A) (i : Pos R U) : A :=
  if h : (finProdFinEquiv i).val < n then f ⟨(finProdFinEquiv i).val, h⟩ else 0

def row (x : Index n → A) (i : Fin R) (p : Pos U n) := pad (fun a => x (0, a, p.2)) (i, p.1)
def col (x : Index n → A) (j : Fin R) (p : Pos n U) := pad (fun b => x (1, p.1, b)) (j, p.2)
def block (x : Index n → A) (s : Pos R R) (p : Pos U U) :=
  pad (fun a => pad (fun b => x (2, a, b)) (s.2, p.2)) (s.1, p.1)

def left (R : ℕ) (x : Index n → A) (t : A) (p : Pos U n) :=
  ∑ i : Fin R, t ^ (R * i.val) * row x i p

def right (R : ℕ) (x : Index n → A) (t : A) (p : Pos n U) :=
  ∑ j : Fin R, t ^ j.val * col x j p

def claimed (R : ℕ) (x : Index n → A) (t : A) (p : Pos U U) :=
  ∑ s : Pos R R, t ^ (finProdFinEquiv s).val * block x s p

def residual (x : Index n → A) (p : Pos U U) (s : Pos R R) :=
  mm (row x s.1) (col x s.2) p - block x s p

theorem expand (x : Index n → A) (t : A) (p : Pos U U) :
    mm (left R x t) (right R x t) p - claimed R x t p =
      ∑ s : Pos R R, t ^ (finProdFinEquiv s).val * residual x p s := by
  simp only [residual, mul_sub, sum_sub_distrib, claimed]
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [mm, left, right, sum_mul_sum]
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  change _ = t ^ (j.val + R * i.val) * _
  rw [pow_add]
  ring

variable {F : Type*} [Field F]

theorem complete {x : Index n → F} (h : Correct x) (p : Pos U U) (s : Pos R R) :
    residual x p s = 0 := by
  unfold residual mm row col block pad
  by_cases hi : (finProdFinEquiv (s.1, p.1)).val < n
  · by_cases hj : (finProdFinEquiv (s.2, p.2)).val < n
    · simp only [dite_eq_left hi, dite_eq_left hj]
      exact sub_eq_zero.mpr (h ⟨_, hi⟩ ⟨_, hj⟩)
    · simp only [dite_eq_left hi, dite_eq_right hj, mul_zero, sum_const_zero, sub_zero]
  · simp only [dite_eq_right hi, zero_mul, sum_const_zero, sub_zero]

private theorem reconstruct (hn : n ≤ R * U) {x : Index n → F}
    (h : ∀ (p : Pos U U) (s : Pos R R), residual x p s = 0) : Correct x := by
  let e (i : Fin n) : Pos R U := finProdFinEquiv.symm (Fin.castLE hn i)
  have he (f : Fin n → F) (i) : pad f (e i) = f i := by
    simp only [pad, e, Equiv.apply_symm_apply, Fin.val_castLE, dite_eq_left i.isLt, Fin.eta]
  intro i j
  have hh := h ((e i).2, (e j).2) ((e i).1, (e j).1)
  simpa only [residual, mm, row, col, block, Prod.mk.eta, he, sub_eq_zero] using hh

/-- Enough distinct successful evaluations force every coefficient
of the block residual to vanish. -/
theorem sound (hn : n ≤ R * U) {L : ℕ} (v : Fin L ↪ F) (x : Index n → F) (hx : ¬ Correct x) :
    #{i | ∀ p : Pos U U, mm (left R x (v i)) (right R x (v i)) p = claimed R x (v i) p} < R * R := by
  by_contra! he
  let S : Finset (Fin L) := {i | ∀ p : Pos U U,
    mm (left R x (v i)) (right R x (v i)) p = claimed R x (v i) p}
  let e : Fin (R * R) ↪ ↥S := (Fin.castLEEmb (show R * R ≤ Fintype.card ↥S by
    rwa [Fintype.card_coe])).trans (Fintype.equivFin S).symm.toEmbedding
  apply hx
  apply reconstruct hn
  intro p s
  let c (i : Fin (R * R)) := residual x p (finProdFinEquiv.symm i)
  have hinj : Function.Injective (fun i => v (e i).val) :=
    v.injective.comp (Subtype.val_injective.comp e.injective)
  have hc : c = 0 := by
    apply Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero hinj
    intro j
    rw [← finProdFinEquiv.sum_comp]
    simp only [c, Equiv.symm_apply_apply]
    rw [← expand, (mem_filter.mp (e j).property).2 p, sub_self]
  simpa only [c, Equiv.symm_apply_apply, Pi.zero_apply] using congrFun hc (finProdFinEquiv s)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-! # Arithmetic instructions and equality tests in a block sketch -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open Finset MvPolynomial
open scoped Classical

variable {F : Type*} [Field F] {n R U : ℕ}

def sketch (n R U : ℕ) (t : F) : Test F n :=
  ⟨U * U, fun i => mm (left R X (C t)) (right R X (C t)) (finProdFinEquiv.symm i),
    fun i => claimed R X (C t) (finProdFinEquiv.symm i)⟩

private theorem eval_pad (x : Index n → F) (z : Pos R U) (f : Fin n → Poly F n) :
    eval x (pad f z) = pad (fun i => eval x (f i)) z := by
  unfold pad; split <;> simp_all

theorem sketch_accept (x : Index n → F) (t : F) :
    (sketch n R U t).accept x ↔
      ∀ p : Pos U U, mm (left R x t) (right R x t) p = claimed R x t p := by
  unfold sketch Test.accept
  simp only [mm, left, right, claimed, row, col, block, map_sum, map_mul, map_pow, eval_C, eval_pad, eval_X]
  constructor
  · intro h p
    simpa only [Equiv.symm_apply_apply] using h (finProdFinEquiv p)
  · exact fun h i => h (finProdFinEquiv.symm i)

private theorem substitute {m : ℕ} (h : Integral.Computes F U U n m) {S : Set (Poly F n)}
    (A : Pos U n → Poly F n) (B : Pos n U → Poly F n)
    (hS : inputs F n ⊆ S) (hA : Set.range A ⊆ S) (hB : Set.range B ⊆ S) :
    CanMake S m (Set.range (mm A B)) := by
  let f := eval₂Hom (C : F →+* Poly F n) (Sum.elim A B)
  obtain ⟨V, hV, hout⟩ := h
  obtain ⟨W, hW, hm⟩ := hV.map (U := S) f (by
    rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · simpa [f] using hS (show C x ∈ inputs F n from Or.inl ⟨x, rfl⟩)
    · rcases x with x | x
      · simpa [f, Integral.input] using hA ⟨x, rfl⟩
      · simpa [f, Integral.input] using hB ⟨x, rfl⟩)
  refine ⟨m, le_rfl, W, hW, ?_⟩
  rintro _ ⟨p, rfl⟩
  simpa [mm, Integral.output, Integral.input, f] using hm _ (hout p)

private theorem pad_mem (z : Pos R U) (f : Fin n → Poly F n) (h : ∀ i, f i ∈ inputs F n) :
    pad f z ∈ inputs F n := by
  unfold pad
  split
  · exact h _
  · exact Or.inl ⟨0, map_zero _⟩

private theorem prepare {I J : Type} [Fintype I] [Fintype J]
    (t : F) (a : I → ℕ) (f : I → J → Poly F n) (h : ∀ i j, f i j ∈ inputs F n) :
    CanMake (inputs F n) (Fintype.card J * (Fintype.card I * 2))
      (Set.range (fun j => ∑ i, (C t) ^ (a i) * f i j)) := by
  apply CanMake.range
  intro j
  exact CanMake.linear (Or.inl ⟨0, map_zero _⟩) (fun i => Or.inl ⟨_, map_pow _ _ _⟩) (fun i => h i j)

/-- The large rectangular multiplication is the only non-linear
part. Each scalar of the padded inputs contributes at most two gates. -/
theorem sketch_cost {m : ℕ} (h : Integral.Computes F U U n m) (t : F) :
    (sketch n R U t).cost (m + 4 * (R : ℝ) * U * n + 2 * ((R : ℝ) * U) ^ 2 + (U : ℝ) ^ 2) := by
  let A : Pos U n → Poly F n := left R X (C t)
  let B : Pos n U → Poly F n := right R X (C t)
  let E : Pos U U → Poly F n := claimed R X (C t)
  have hX (i) : X i ∈ inputs F n := Or.inr ⟨i, rfl⟩
  have hA : CanMake (inputs F n) (U * n * (R * 2)) (Set.range A) := by
    unfold A left
    simpa only [Pos, Fintype.card_prod, Fintype.card_fin] using
      prepare t (fun i : Fin R => R * i.val) (row (U := U) X) (fun _ _ => pad_mem _ _ (fun _ => hX _))
  have hB : CanMake (inputs F n) (n * U * (R * 2)) (Set.range B) := by
    unfold B right
    simpa only [Pos, Fintype.card_prod, Fintype.card_fin] using
      prepare t (fun i : Fin R => i.val) (col (U := U) X) (fun _ _ => pad_mem _ _ (fun _ => hX _))
  have hE : CanMake (inputs F n) (U * U * (R * R * 2)) (Set.range E) := by
    unfold E claimed
    simpa only [Pos, Fintype.card_prod, Fintype.card_fin] using
      prepare t (fun i : Pos R R => (finProdFinEquiv i).val) (block (U := U) X)
        (fun _ _ => pad_mem _ _ (fun _ => pad_mem _ _ (fun _ => hX _)))
  have hp := (hA.union hB).keep.trans (substitute h A B Set.subset_union_left
    (fun _ hx => Or.inr (Or.inl hx)) (fun _ hx => Or.inr (Or.inr hx)))
  obtain ⟨l, hl, V, hV, hv⟩ := hp.union hE
  refine ⟨l, V, hV, fun i => ⟨hv (Or.inl ⟨_, rfl⟩), hv (Or.inr ⟨_, rfl⟩)⟩, ?_⟩
  have hh := (Nat.cast_le (α := ℝ)).mpr hl
  change (l : ℝ) + (U * U : ℕ) ≤ _
  push_cast at hh ⊢
  linarith only [hh]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-! Simulating each seed separately preserves its decision and probability. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

open Filter Finset
open scoped Classical
variable {F : Type*} [Field F] {ρ η v : ℝ}

theorem Support.tree_possible (h : Support F ρ v) : TreeSupportPossible F ρ v := by
  intro ε hε
  filter_upwards [h ε hε (1 / 3) (by norm_num)] with n hn
  obtain ⟨L, A, hL, size, cost, on, off⟩ := hn
  choose V hv he using fun i => (A i).tree (cost i)
  have pos : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  let u := (L : ℝ)⁻¹
  have mass : (∑ _ : Fin L, u) = 1 := by simp [u, pos.ne']
  refine ⟨Fin L, inferInstance, fun _ => u, fun _ => 0, V, by simpa using size, fun _ => (inv_pos.mpr pos).le,
    mass ▸ hasSum_fintype _, hv, ?_⟩
  intro x
  simp only [tsum_fintype, he]
  by_cases hx : Correct x
  · simp only [hx, on x hx, ite_true, mass]
    norm_num
  · simp only [hx, iff_false, ite_not]
    have loss : (∑ i, if (A i).accept x then u else 0) ≤ 1 / 3 := by
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      exact (div_le_iff₀ pos).mpr (off x hx)
    have eq (i) : (if (A i).accept x then 0 else u) =
        u - (if (A i).accept x then u else 0) := by split <;> simp
    simp_rw [eq]
    rw [sum_sub_distrib, mass]
    linarith

theorem Entropy.tree_possible (h : Entropy F η v) : TreeEntropyPossible F η v := by
  intro ε hε
  filter_upwards [h ε hε] with n hn
  obtain ⟨L, A, w, hw, mass, budget, cost, correct⟩ := hn
  choose V hv he using fun i => (A i).tree (cost i)
  refine ⟨Fin L, inferInstance, w, fun _ => 0, V, ⟨_, hasSum_fintype _, ?_⟩, hw, mass ▸ hasSum_fintype w, hv, ?_⟩
  · simpa only [neg_mul, sum_neg_distrib] using budget
  · intro x
    simpa only [tsum_fintype, he] using correct x

private theorem paths {n : ℕ} {ι : Type} {w : ι → ℝ} {t : ι → ℕ} (A : ∀ i, Tree F n (t i))
    {c : ℝ} (hc : ∀ i, ((A i).depth : ℝ) ≤ c) (ha : Accurate w (fun i => (A i).accept) Correct) :
    ∃ V : ι → Verifier F n, (∀ i, (V i).cost c) ∧ Accurate w (fun i => (V i).accept) Correct := by
  choose V hv he using fun i => (A i).simulate
  refine ⟨V, fun i p hp => (hv i p hp).trans (hc i), ?_⟩
  simpa only [he] using ha

theorem TreeSupportPossible.possible (h : TreeSupportPossible F ρ v) : SupportPossible F ρ v := by
  intro ε he
  filter_upwards [h ε he] with n hn
  obtain ⟨ι, _, w, t, A, hb, hw, hs, hc, ha⟩ := hn
  obtain ⟨V, hv, ha⟩ := paths A hc ha
  exact ⟨ι, inferInstance, w, V, hb, hw, hs, hv, ha⟩

theorem TreeEntropyPossible.possible (h : TreeEntropyPossible F η v) : EntropyPossible F η v := by
  intro ε he
  filter_upwards [h ε he] with n hn
  obtain ⟨ι, _, w, t, A, hb, hw, hs, hc, ha⟩ := hn
  obtain ⟨V, hv, ha⟩ := paths A hc ha
  exact ⟨ι, inferInstance, w, V, hb, hw, hs, hv, ha⟩

theorem Support.possible (h : Support F ρ v) : SupportPossible F ρ v := h.tree_possible.possible

theorem Entropy.possible (h : Entropy F η v) : EntropyPossible F η v := h.tree_possible.possible

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

section
/-!
# The rectangular expression in the verification characterization

This evaluates the tradeoff and both critical budgets from the last
paragraph of Section 8. Identifying the rectangular expression with
the cost of randomized arithmetic and equality-test trees is a
separate theorem of the cited work on verification.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

variable {F : Type*} [Field F]

theorem shape {k : ℝ} (hk : 0 ≤ k) (hk' : k ≤ 1) : U k k 1 = (1 + k / 2) ^ 2 := by
  rcases eq_or_lt_of_le hk with rfl | hk
  · norm_num [U, benchmark]
  rcases eq_or_lt_of_le hk' with rfl | hk'
  · norm_num [U, benchmark]
  rw [U, min_self, ite_eq_right hk'.not_ge, ite_eq_left le_rfl, benchmark, max_eq_left (by nlinarith)]
  field_simp
  ring

theorem support_formula (hr : Rigidity F) (hs : MatrixExponent.omega F = 9 / 4)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 2) :
    max 2 (exponent F (1 - ρ / 2) (1 - ρ / 2) 1) = max 2 ((3 / 2 - ρ / 4) ^ 2) := by
  have hk : 0 ≤ 1 - ρ / 2 := by linarith
  rw [all_shapes hr hs hk hk zero_le_one, shape hk (by linarith)]
  congr 1
  ring

theorem entropy_formula (hr : Rigidity F) (hs : MatrixExponent.omega F = 9 / 4)
    {η : ℝ} (hη : 0 ≤ η) :
    let ρ := min (3 * η) 2
    max 2 (exponent F (1 - ρ / 2) (1 - ρ / 2) 1) = max 2 ((3 / 2 - ρ / 4) ^ 2) :=
  support_formula hr hs (le_min (by positivity) (by norm_num)) (min_le_right _ _)

private theorem critical_mem : 6 - 4 * Real.sqrt 2 ∈ Set.Icc (0 : ℝ) 2 := by
  have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg 2
  constructor <;> nlinarith

theorem support_threshold {ρ : ℝ} (hρ : ρ ≤ 2) :
    max 2 ((3 / 2 - ρ / 4) ^ 2) = 2 ↔ 6 - 4 * Real.sqrt 2 ≤ ρ := by
  rw [max_eq_left_iff, ← Real.le_sqrt (by linarith) (by norm_num)]
  constructor <;> intro h <;> linarith

theorem entropy_threshold (η : ℝ) :
    max 2 ((3 / 2 - min (3 * η) 2 / 4) ^ 2) = 2 ↔ (6 - 4 * Real.sqrt 2) / 3 ≤ η := by
  rw [support_threshold (min_le_right _ _), le_min_iff, and_iff_left critical_mem.2]
  constructor <;> intro h <;> linarith

theorem least_support (hr : Rigidity F) (hs : MatrixExponent.omega F = 9 / 4) :
    IsLeast {ρ ∈ Set.Icc 0 2 | max 2 (exponent F (1 - ρ / 2) (1 - ρ / 2) 1) = 2}
      (6 - 4 * Real.sqrt 2) := by
  have he (ρ : ℝ) (hρ : ρ ∈ Set.Icc 0 2) :
      max 2 (exponent F (1 - ρ / 2) (1 - ρ / 2) 1) = 2 ↔ 6 - 4 * Real.sqrt 2 ≤ ρ := by
    rw [support_formula hr hs hρ.1 hρ.2, support_threshold hρ.2]
  exact ⟨⟨critical_mem, (he _ critical_mem).mpr le_rfl⟩, fun ρ h => (he ρ h.1).mp h.2⟩

theorem least_entropy (hr : Rigidity F) (hs : MatrixExponent.omega F = 9 / 4) :
    IsLeast {η : ℝ | 0 ≤ η ∧ max 2 (exponent F (1 - min (3 * η) 2 / 2) (1 - min (3 * η) 2 / 2) 1) = 2}
      ((6 - 4 * Real.sqrt 2) / 3) := by
  have he (η : ℝ) (hη : 0 ≤ η) :
      max 2 (exponent F (1 - min (3 * η) 2 / 2) (1 - min (3 * η) 2 / 2) 1) = 2 ↔
      (6 - 4 * Real.sqrt 2) / 3 ≤ η := by
    rw [entropy_formula hr hs hη, entropy_threshold]
  have h : 0 ≤ (6 - 4 * Real.sqrt 2) / 3 := div_nonneg critical_mem.1 (by norm_num)
  exact ⟨⟨h, (he _ h).mpr le_rfl⟩, fun η hη => (he η hη.1).mp hη.2⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-! # From a rectangular algorithm to uniform public-seed verification -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open Finset Filter
open scoped Classical

variable {F : Type*} [Field F] [Infinite F]

private theorem uniform {n U R m L : ℕ} {s c p : ℝ}
    (h : Integral.Computes F U U n m) (hn : n ≤ R * U) (hL : 0 < L) (hs : (L : ℝ) ≤ s)
    (hc : m + 4 * (R : ℝ) * U * n + 2 * ((R : ℝ) * U) ^ 2 + (U : ℝ) ^ 2 ≤ c) (hp : (R : ℝ) * R ≤ p * L) :
    Uniform F n s c p := by
  let v : Fin L ↪ F := Fin.valEmbedding.trans (Infinite.natEmbedding F)
  refine ⟨L, fun i => sketch n R U (v i), hL, hs, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨k, V, hV, hout, hk⟩ := sketch_cost h (R := R) (v i)
    exact ⟨k, V, hV, hout, hk.trans hc⟩
  · intro x hx i
    apply (sketch_accept x _).mpr
    intro z
    rw [← sub_eq_zero, expand]
    simp only [complete hx, mul_zero, sum_const_zero]
  · intro x hx
    simp only [sketch_accept]
    apply le_trans _ hp
    exact_mod_cast (sound hn v x hx).le

private theorem dimensions {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 2) {n : ℕ} (hn : 0 < n) :
    let R := side n (ρ / 2)
    let U := side n (1 - ρ / 2)
    n ≤ R * U ∧ (R : ℝ) * R ≤ 4 * (n : ℝ) ^ ρ ∧
      4 * (R : ℝ) * U * n + 2 * ((R : ℝ) * U) ^ 2 + (U : ℝ) ^ 2 ≤ 64 * (n : ℝ) ^ 2 := by
  let R := side n (ρ / 2)
  let U := side n (1 - ρ / 2)
  have hn' : 0 < (n : ℝ) := by positivity
  have hr : (R : ℝ) ≤ 2 * (n : ℝ) ^ (ρ / 2) := side_le hn (by linarith)
  have hu : (U : ℝ) ≤ 2 * (n : ℝ) ^ (1 - ρ / 2) := side_le hn (by linarith)
  have he : (n : ℝ) ^ (ρ / 2) * (n : ℝ) ^ (1 - ρ / 2) = n := by rw [← Real.rpow_add hn', add_sub_cancel, Real.rpow_one]
  have hm : (R : ℝ) * U ≤ 4 * n := by
    have hh := mul_le_mul hr hu (by positivity) (by positivity)
    linarith only [he, hh]
  have hbound : (U : ℝ) ≤ 4 * n :=
    (le_mul_of_one_le_left (by positivity) (by exact_mod_cast side_pos hn (ρ / 2))).trans hm
  refine ⟨?_, ?_, ?_⟩
  · have hh : (n : ℝ) ≤ (R : ℝ) * U := he.ge.trans
      (mul_le_mul (Nat.le_ceil _) (Nat.le_ceil _) (by positivity) (by positivity))
    exact_mod_cast hh
  · calc
      _ ≤ (2 * (n : ℝ) ^ (ρ / 2)) ^ 2 := by rw [pow_two]; gcongr
      _ = _ := by rw [mul_pow, ← Real.rpow_mul_natCast hn'.le]; norm_num
  · calc
      _ = 4 * ((R : ℝ) * U) * n + 2 * ((R : ℝ) * U) ^ 2 + (U : ℝ) ^ 2 := by ring
      _ ≤ 4 * (4 * (n : ℝ)) * n + 2 * (4 * (n : ℝ)) ^ 2 + (4 * (n : ℝ)) ^ 2 := by gcongr
      _ = _ := by ring

theorem support_of_rectangles {ρ v : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 2)
    (h : Integral.Admissible F (1 - ρ / 2) (1 - ρ / 2) 1 v) : Support F ρ (max 2 v) := by
  intro ε hε p hp
  obtain ⟨C, hC, hm⟩ := h (ε / 2) (half_pos hε)
  obtain ⟨J, hJ⟩ := exists_nat_gt (1 / p)
  have hj : 0 < J := Nat.cast_pos.mp ((by positivity : 0 < 1 / p).trans hJ)
  have hp' : 1 ≤ p * J := by rw [mul_comm]; exact (div_le_iff₀ hp).mp hJ.le
  have grow (e : ℝ) (he : 0 < e) := (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0, (grow ε hε).eventually_ge_atTop (4 * J),
    (grow (ε / 2) (half_pos hε)).eventually_ge_atTop (C + 64)] with n hn hs hc
  let R := side n (ρ / 2)
  let U := side n (1 - ρ / 2)
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < R := side_pos hn _
  obtain ⟨hlo, hsize, hcost⟩ := dimensions hρ hρ' hn
  obtain ⟨m, hcomp, hb⟩ := hm n hn
  rw [show Integral.side n 1 = n from side_one n] at hcomp
  refine uniform (L := J * (R * R)) hcomp hlo (by positivity) ?_ ?_ ?_
  · rw [Nat.cast_mul, Nat.cast_mul, Real.rpow_add (by positivity)]
    calc
      _ ≤ J * (4 * (n : ℝ) ^ ρ) := mul_le_mul_of_nonneg_left hsize (by positivity)
      _ = (n : ℝ) ^ ρ * (4 * J) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
  · calc
      _ ≤ C * (n : ℝ) ^ (v + ε / 2) + 64 * (n : ℝ) ^ 2 := by linarith
      _ ≤ C * (n : ℝ) ^ (max 2 v + ε / 2) + 64 * (n : ℝ) ^ (max 2 v + ε / 2) := by
        rw [← Real.rpow_two]
        gcongr <;> linarith [le_max_left 2 v, le_max_right 2 v]
      _ = (C + 64) * (n : ℝ) ^ (max 2 v + ε / 2) := by ring
      _ ≤ (n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (max 2 v + ε / 2) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
  · rw [Nat.cast_mul, Nat.cast_mul, ← mul_assoc]
    exact le_mul_of_one_le_left (by positivity) hp'

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

section
/-!
# The cost forced by independent output combinations

The finite bound uses the actual field exponent. At the benchmark,
the bound yields the verification tradeoff whenever a verifier
provides enough independent output combinations at low border rank.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open Filter

variable {F : Type*} [Field F] {n q r : ℕ}

theorem Projected.size (h : Projected F n q r) : q ≤ n * n := by
  obtain ⟨P, hq, _⟩ := h
  simpa [Pos] using hq.trans P.rank_le_card_width

private theorem log_size (h : Projected F n q r) (hn : 0 < n) (hq : 0 < q) :
    Real.log q / 2 ≤ Real.log n := by
  have he := Real.log_le_log (Nat.cast_pos.mpr hq) (show (q : ℝ) ≤ (n : ℝ) * n by exact_mod_cast h.size)
  rw [Real.log_mul (by positivity) (by positivity)] at he
  linarith

variable [Infinite F]

theorem Projected.lower (h : Projected F n q r) (hn : 0 < n) (hq : 0 < q) :
    Real.exp (exponent F (Real.log q / 2) (Real.log q / 2) (Real.log n)) ≤ r := by
  obtain ⟨S, he, hcut⟩ := h.cells
  have hS : S.Nonempty := Finset.card_pos.mp (he.symm ▸ hq)
  have hv (x y z) : mask (ordinary F n n n) S x y z ≠ 0 ↔ (x, y) ∈ S := by simp [mask, ordinary]
  have hh := hcut.cells hS hv hn hn hn
  rw [he, short, min_self, min_eq_right (log_size h hn hq),
    show Real.log (q : ℝ) - Real.log q / 2 = Real.log q / 2 by ring] at hh
  exact hh

private theorem finite_rate (hr : Rigidity F) (hs : MatrixExponent.omega F = 9 / 4)
    {L : ℕ} {ρ v ε : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 2) (hε : 0 < ε)
    (hn : 2 ≤ n) (hL : (L : ℝ) ≤ (n : ℝ) ^ (ρ + ε)) (hv : (r : ℝ) ≤ (n : ℝ) ^ (v + ε))
    (harea : n * n ≤ L * q) (hp : Projected F n q r) : (3 / 2 - ρ / 4) ^ 2 ≤ v + 2 * ε := by
  have hn' : 1 < (n : ℝ) := by exact_mod_cast hn
  have hq : 0 < q := (Nat.pos_of_mul_pos_left ((Nat.mul_pos (by omega) (by omega)).trans_le harea))
  let t := Real.log (n : ℝ)
  have ht : 0 < t := Real.log_pos hn'
  let k := (Real.log (q : ℝ) / 2) / t
  have hk : 0 ≤ k := div_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast hq)) (by norm_num)) ht.le
  have hk' : k ≤ 1 := (div_le_one ht).mpr (log_size hp (by omega) hq)
  have he : t * k = Real.log (q : ℝ) / 2 := mul_div_cancel₀ _ ht.ne'
  have lower : 1 - ρ / 2 - ε / 2 ≤ k := by
    have hb := (show (n : ℝ) * n ≤ (L : ℝ) * q by exact_mod_cast harea).trans
      (mul_le_mul_of_nonneg_right hL (by positivity))
    have hh := Real.log_le_log (by positivity) hb
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow (by positivity)] at hh
    apply le_of_mul_le_mul_left _ ht
    rw [he]
    unfold t
    linarith only [hh]
  have upper : (1 + k / 2) ^ 2 ≤ v + ε := by
    have h := (hp.lower (by omega) hq).trans hv
    rw [Real.rpow_def_of_pos (by positivity), Real.exp_le_exp] at h
    have e := homogeneous F hk hk zero_le_one ht.le
    rw [he, mul_one, all_shapes hr hs hk hk zero_le_one, shape hk hk'] at e
    exact le_of_mul_le_mul_left (e.ge.trans h) ht
  let x := 3 / 2 - ρ / 4
  let y := 1 + k / 2
  have hxy : 0 ≤ x + y ∧ x + y ≤ 3 := by unfold x y; constructor <;> linarith
  have hsub : x - y ≤ ε / 4 := by unfold x y; linarith
  have hh := mul_le_mul hsub hxy.2 hxy.1 (show 0 ≤ ε / 4 by positivity)
  change y ^ 2 ≤ v + ε at upper
  change x ^ 2 ≤ v + 2 * ε
  linarith only [hh, upper, hε]

theorem profile_lower (hr : Rigidity F) (hs : MatrixExponent.omega F = 9 / 4)
    {ρ v : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 2) (hv : 2 ≤ v)
    (h : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∃ L q r : ℕ, (L : ℝ) ≤ (n : ℝ) ^ (ρ + ε) ∧
      (r : ℝ) ≤ (n : ℝ) ^ (v + ε) ∧ n * n ≤ L * q ∧ Projected F n q r) :
    max 2 ((3 / 2 - ρ / 4) ^ 2) ≤ v := by
  refine max_le hv (le_of_forall_pos_le_add fun ε hε => ?_)
  obtain ⟨n, hn, L, q, r, hL, hv', ha, hp⟩ := ((eventually_ge_atTop 2).and (h (ε / 2) (half_pos hε))).exists
  linarith only [finite_rate hr hs hρ hρ' (half_pos hε) hn hL hv' ha hp]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# Public-seed verification lower bounds

Both budgets give a finite set of seeds with a strict acceptance
gap. Its size bounds the loss of independent output combinations.
Reading entries gives a quadratic bound even for large seed sets.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open Filter Finset
open scoped Classical

variable {F : Type*} [Field F] {ρ η v : ℝ}

private def Retained (F : Type*) [Field F] (ρ v : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∃ (ι : Type) (w : ι → ℝ) (A : ι → Verifier F n) (S : Finset ι),
      (S.card : ℝ) ≤ (n : ℝ) ^ (ρ + ε) ∧ (∀ i, 0 ≤ w i) ∧ HasSum w 1 ∧
        (∀ i, (A i).cost ((n : ℝ) ^ (v + ε))) ∧ Accurate w (fun i => (A i).accept) Correct ∧
        Gap w (fun i => (A i).accept) Correct S

private theorem of_support (h : SupportPossible F ρ v) : Retained F ρ v := by
  intro ε he
  filter_upwards [h ε he] with n hn
  obtain ⟨ι, _, w, A, hsize, hw, hs, hc, ha⟩ := hn
  exact ⟨ι, w, A, univ, hsize, hw, hs, hc, ha, finite_gap hw hs ha⟩

private theorem of_entropy (h : EntropyPossible F η v) (hη : 0 ≤ η) : Retained F (3 * η) v := by
  intro ε he
  filter_upwards [h (ε / 4) (by positivity), eventually_ge_atTop 2] with n hn h₂
  obtain ⟨ι, _, w, A, ⟨E, hE, hb⟩, hw, hs, hc, ha⟩ := hn
  obtain ⟨S, _, hcard, hgap⟩ := entropy_gap hw hs ha hE h₂ hη he hb
  refine ⟨ι, w, A, S, hcard, hw, hs, ?_, ha, hgap⟩
  intro i p hp
  exact (hc i p hp).trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega)) (by linarith))

private theorem absorb (v c : ℝ) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ (v + ε / 2) < (n : ℝ) ^ (v + ε) := by
  have h := (tendsto_rpow_atTop (half_pos he)).comp tendsto_natCast_atTop_atTop
  filter_upwards [h.eventually_gt_atTop c, eventually_gt_atTop 0] with n hn hp
  have nh : 0 < (n : ℝ) := Nat.cast_pos.mpr hp
  calc
    _ < (n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (v + ε / 2) := mul_lt_mul_of_pos_right hn (by positivity)
    _ = _ := by rw [← Real.rpow_add nh]; congr 1; ring

private theorem quadratic (h : Retained F ρ v) : 2 ≤ v := by
  by_contra! hv
  have hp : 0 < 2 - v := sub_pos.mpr hv
  obtain ⟨n, ⟨ι, w, A, _, _, hw, hs, hc, ha, _⟩, hn⟩ := ((h _ (half_pos hp)).and (absorb v 9 hp)).exists
  rw [show v + (2 - v) = 2 by ring, Real.rpow_two] at hn
  exact hn.not_ge (read_bound hw hs A hc ha)

variable [IsAlgClosed F] [CharZero F]

private theorem gap_lower (h : Retained F ρ v) (hr : Rigidity F) (hs : MatrixExponent.omega F = 9 / 4)
    (hρ : 0 ≤ ρ) (ht : ρ ≤ 2) : max 2 ((3 / 2 - ρ / 4) ^ 2) ≤ v := by
  apply profile_lower hr hs hρ ht (quadratic h)
  intro ε he
  filter_upwards [h _ (half_pos he), absorb v 4 he, eventually_ge_atTop 1] with n hn hp h₁
  obtain ⟨ι, w, A, S, hcard, hw, _, hc, _, hg⟩ := hn
  obtain ⟨q, r, hcost, hsize, hrank⟩ := gap_projection (show 0 < n by omega) (fun i _ => hw i) (fun i _ => hc i) hg
  refine ⟨S.card, q, r, ?_, hcost.trans hp.le, hsize, hrank⟩
  exact hcard.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast h₁) (by linarith))

theorem SupportPossible.lower (h : SupportPossible F ρ v) (hr : Rigidity F) (hs : MatrixExponent.omega F = 9 / 4)
    (hρ : 0 ≤ ρ) (ht : ρ ≤ 2) : max 2 ((3 / 2 - ρ / 4) ^ 2) ≤ v :=
  gap_lower (of_support h) hr hs hρ ht

theorem EntropyPossible.lower (h : EntropyPossible F η v) (hr : Rigidity F) (hs : MatrixExponent.omega F = 9 / 4)
    (hη : 0 ≤ η) : max 2 ((3 / 2 - min (3 * η) 2 / 4) ^ 2) ≤ v := by
  have he := of_entropy h hη
  by_cases ht : 3 * η ≤ 2
  · rw [min_eq_left ht]
    exact gap_lower he hr hs (by positivity) ht
  · rw [min_eq_right (le_of_not_ge ht)]
    norm_num
    exact quadratic he

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end
