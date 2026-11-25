import OAI.LinearAlgebra.TensorSpectrum.AdditiveCone.Interval
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite rational alternatives

Fourier–Motzkin elimination proves the rational Farkas alternative directly.
The proof keeps the nonnegative combination of original rows at every
elimination step.  Consequently the obstruction has rational coefficients;
neither a real separation theorem nor a rational-density premise is assumed.
-/

open scoped BigOperators

namespace OAI.LinearAlgebra.TensorSpectrum.AdditiveCone

universe u

/-- A negative constant obtained as a nonnegative rational combination of rows. -/
structure RationalCertificate {ι : Type u} [Fintype ι] {n : ℕ}
    (a : ι → Fin n → ℚ) (b : ι → ℚ) where
  weight : ι → ℚ
  nonneg : ∀ i, 0 ≤ weight i
  cancel : ∀ k, ∑ i, weight i * a i k = 0
  negative : ∑ i, weight i * b i < 0

theorem weighted_sum_assoc {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : κ → ℚ) (w : κ → ι → ℚ) (v : ι → ℚ) :
    (∑ i, (∑ j, d j * w j i) * v i) =
      ∑ j, d j * (∑ i, w j i * v i) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private abbrev EliminationIndex {ι : Type u} {n : ℕ}
    (a : ι → Fin (n + 1) → ℚ) :=
  {i : ι // a i 0 = 0} ⊕
    ({i : ι // 0 < a i 0} × {i : ι // a i 0 < 0})

private noncomputable def eliminationWeight {ι : Type u} {n : ℕ}
    (a : ι → Fin (n + 1) → ℚ) (j : EliminationIndex a) (i : ι) : ℚ := by
  classical
  exact match j with
  | Sum.inl z => if i = z.val then 1 else 0
  | Sum.inr p =>
      (if i = p.1.val then -a p.2.val 0 else 0) +
      (if i = p.2.val then a p.1.val 0 else 0)

private theorem eliminationWeight_nonneg {ι : Type u} {n : ℕ}
    (a : ι → Fin (n + 1) → ℚ) (j : EliminationIndex a) (i : ι) :
    0 ≤ eliminationWeight a j i := by
  classical
  cases j with
  | inl z => simp only [eliminationWeight]; split <;> norm_num
  | inr p =>
      simp only [eliminationWeight]
      apply add_nonneg
      · split
        · exact neg_nonneg.mpr p.2.property.le
        · exact le_rfl
      · split
        · exact p.1.property.le
        · exact le_rfl

private theorem eliminationWeight_zero {ι : Type u} [Fintype ι] {n : ℕ}
    (a : ι → Fin (n + 1) → ℚ) (z : {i : ι // a i 0 = 0})
    (v : ι → ℚ) :
    (∑ i, eliminationWeight a (Sum.inl z) i * v i) = v z.val := by
  classical
  simp [eliminationWeight]

private theorem eliminationWeight_pair {ι : Type u} [Fintype ι] {n : ℕ}
    (a : ι → Fin (n + 1) → ℚ)
    (p : {i : ι // 0 < a i 0} × {i : ι // a i 0 < 0}) (v : ι → ℚ) :
    (∑ i, eliminationWeight a (Sum.inr p) i * v i) =
      (-a p.2.val 0) * v p.1.val + a p.1.val 0 * v p.2.val := by
  classical
  simp [eliminationWeight, add_mul, Finset.sum_add_distrib, ite_mul]

private theorem eliminationWeight_head {ι : Type u} [Fintype ι] {n : ℕ}
    (a : ι → Fin (n + 1) → ℚ) (j : EliminationIndex a) :
    (∑ i, eliminationWeight a j i * a i 0) = 0 := by
  cases j with
  | inl z => rw [eliminationWeight_zero]; exact z.property
  | inr p => rw [eliminationWeight_pair]; ring

/-- A finite rational affine system has a solution or a rational obstruction.
    The alternatives are constructed by elimination of one coordinate at a time. -/
theorem rational_alternative (n : ℕ) :
    ∀ {ι : Type u} [Fintype ι] (a : ι → Fin n → ℚ) (b : ι → ℚ),
      (∃ x : Fin n → ℚ, ∀ i, 0 ≤ (∑ k, a i k * x k) + b i) ∨
        Nonempty (RationalCertificate a b) := by
  classical
  induction n with
  | zero =>
      intro ι _ a b
      by_cases h : ∀ i, 0 ≤ b i
      · left
        exact ⟨Fin.elim0, by simpa using h⟩
      · right
        obtain ⟨i, hi⟩ := not_forall.mp h
        have hi : b i < 0 := lt_of_not_ge hi
        refine ⟨{
          weight := fun j => if j = i then 1 else 0
          nonneg := ?_
          cancel := ?_
          negative := ?_
        }⟩
        · intro j; split <;> norm_num
        · intro k; exact Fin.elim0 k
        · simpa using hi
  | succ n ih =>
      intro ι _ a b
      let J := EliminationIndex a
      let : Fintype J := inferInstanceAs (Fintype (EliminationIndex a))
      let w : J → ι → ℚ := eliminationWeight a
      let a' : J → Fin n → ℚ := fun j k => ∑ i, w j i * a i k.succ
      let b' : J → ℚ := fun j => ∑ i, w j i * b i
      rcases ih a' b' with h | hc
      · obtain ⟨x, hx⟩ := h
        let residual : ι → ℚ := fun i => (∑ k, a i k.succ * x k) + b i
        have hres (j : J) : 0 ≤ ∑ i, w j i * residual i := by
          have heq : (∑ i, w j i * residual i) =
              (∑ k, a' j k * x k) + b' j := by
            simp only [residual, mul_add, Finset.sum_add_distrib, b', a']
            congr 1
            simp_rw [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k hk
            apply Finset.sum_congr rfl
            intro i hi
            ring
          rw [heq]
          exact hx j
        have hz : ∀ i, a i 0 = 0 → 0 ≤ residual i := by
          intro i hi
          have h := hres (Sum.inl ⟨i, hi⟩)
          simpa only [w, eliminationWeight_zero] using h
        have hp : ∀ i j, 0 < a i 0 → a j 0 < 0 →
            0 ≤ (-a j 0) * residual i + a i 0 * residual j := by
          intro i j hi hj
          have h := hres (Sum.inr (⟨i, hi⟩, ⟨j, hj⟩))
          simpa only [w, eliminationWeight_pair] using h
        obtain ⟨x₀, hx₀⟩ := TensorSpectrum.exists_nonneg_affine_of_pairwise
          (fun i => a i 0) residual hz hp
        left
        refine ⟨Fin.cases x₀ x, ?_⟩
        intro i
        simpa only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
          residual, add_assoc] using hx₀ i
      · let c := Classical.choice hc
        right
        refine ⟨{
          weight := fun i => ∑ j, c.weight j * w j i
          nonneg := ?_
          cancel := ?_
          negative := ?_
        }⟩
        · intro i
          exact Finset.sum_nonneg fun j hj =>
            mul_nonneg (c.nonneg j) (eliminationWeight_nonneg a j i)
        · intro k
          refine Fin.cases ?_ (fun k => ?_) k
          · rw [weighted_sum_assoc]
            have hhead (j : J) : (∑ i, w j i * a i 0) = 0 :=
              eliminationWeight_head a j
            simp_rw [hhead, mul_zero]
            simp
          · rw [weighted_sum_assoc]
            exact c.cancel k
        · rw [weighted_sum_assoc]
          exact c.negative

/-- Infeasibility produces an actual certificate, rather than an assumed
    separation functional or a real coefficient vector. -/
theorem rational_certificate_of_infeasible {ι : Type u} [Fintype ι] {n : ℕ}
    (a : ι → Fin n → ℚ) (b : ι → ℚ)
    (h : ¬ ∃ x : Fin n → ℚ, ∀ i, 0 ≤ (∑ k, a i k * x k) + b i) :
    Nonempty (RationalCertificate a b) := by
  rcases rational_alternative n a b with hs | hc
  · exact False.elim (h hs)
  · exact hc

end OAI.LinearAlgebra.TensorSpectrum.AdditiveCone
