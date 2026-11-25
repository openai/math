import OAI.LinearAlgebra.FiniteFourier.CircuitReindex
import OAI.LinearAlgebra.FiniteFourier.LayerSynchronization

/-! # Grouping bounded tensor factors into pairs

Pairing axes lets a construction on local widths at least four handle
arbitrary widths at least two. One dummy binary axis suffices in odd length.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped Kronecker
noncomputable section

/-- Uniform size estimate for prescribed square factors whose widths lie in
the closed interval from `lo` to `hi`. The constant is independent of the
widths, the number of factors, and their entries. -/
def BoundedGridTensorEstimate (R : Type*) [CommSemiring R] (lo hi : ℕ) (β C : ℝ) : Prop :=
  ∀ (k : ℕ) (n : Fin k → ℕ), (∀ i, lo ≤ n i ∧ n i ≤ hi) →
    ∀ A : (i : Fin k) → Matrix (Fin (n i)) (Fin (n i)) R,
      (complexity (gridTensor A) : ℝ) ≤ C * (↑(∏ i, n i) : ℝ) * (1 + (k : ℝ))^β

variable {R : Type*} [CommSemiring R]

/-- Pair axis `i` in the first half with its counterpart in the second.
The matrix of each pair is its local Kronecker product. -/
private theorem pairedGrid_bound {d k m : ℕ} {β C : ℝ}
    (hp : BoundedGridTensorEstimate R 4 (d^2) β C)
    (hk : k = m+m) (n : Fin k → ℕ) (hn : ∀ i, 2 ≤ n i ∧ n i ≤ d)
    (A : (i : Fin k) → Matrix (Fin (n i)) (Fin (n i)) R) :
    (complexity (gridTensor A) : ℝ) ≤ C * (↑(∏ i, n i) : ℝ) * (1 + (m : ℝ))^β := by
  classical
  subst k
  let l := Fin.castAdd m (n := m)
  let r := Fin.natAdd m (m := m)
  let b (i : Fin m) := n (l i) * n (r i)
  let e (i : Fin m) : Fin (n (l i)) × Fin (n (r i)) ≃ Fin (b i) := finProdFinEquiv
  let B (i : Fin m) := Matrix.reindex (e i) (e i) (A (l i) ⊗ₖ A (r i))
  have hb (i : Fin m) : 4 ≤ b i ∧ b i ≤ d^2 :=
    ⟨Nat.mul_le_mul (hn (l i)).1 (hn (r i)).1, by
      simpa only [b, pow_two] using Nat.mul_le_mul (hn (l i)).2 (hn (r i)).2⟩
  let f : (∀ i, Fin (n i)) ↪ (∀ i, Fin (b i)) :=
    ⟨fun x i => e i (x (l i), x (r i)), by
      intro x y h
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · exact congrArg Prod.fst ((e i).injective (congrFun h i))
      · exact congrArg Prod.snd ((e i).injective (congrFun h i))⟩
  have hAB : (gridTensor B).submatrix f f = gridTensor A := by
    ext x y
    change (∏ i : Fin m, (A (l i) ⊗ₖ A (r i))
      ((e i).symm (e i (x (l i), x (r i)))) ((e i).symm (e i (y (l i), y (r i))))) =
      ∏ i, A i (x i) (y i)
    simp [Fin.prod_univ_add, Finset.prod_mul_distrib, l, r]
  have hcost : complexity (gridTensor A) ≤ complexity (gridTensor B) := by
    rw [← hAB]
    exact (complexity_le_iff ..).mpr ((realizableAtMost_complexity _).submatrix f f)
  have hV : (∏ i, b i) = ∏ i, n i := by
    simp only [b, l, r, Fin.prod_univ_add, Finset.prod_mul_distrib]
  exact (Nat.cast_le (α := ℝ) |>.mpr hcost).trans (by simpa only [hV] using hp m b hb B)

/-- Fixing the extra binary coordinate at zero restricts a tensor product with
an extra identity factor to the original transform. -/
private theorem padBinaryGrid {k : ℕ} (n : Fin k → ℕ)
    (A : (i : Fin k) → Matrix (Fin (n i)) (Fin (n i)) R) :
    ∃ B : (i : Fin (k+1)) →
        Matrix (Fin (Fin.cons (α := fun _ => ℕ) 2 n i)) (Fin (Fin.cons (α := fun _ => ℕ) 2 n i)) R,
      complexity (gridTensor A) ≤ complexity (gridTensor B) := by
  let B : (i : Fin (k+1)) →
      Matrix (Fin (Fin.cons (α := fun _ => ℕ) 2 n i)) (Fin (Fin.cons (α := fun _ => ℕ) 2 n i)) R :=
    Fin.cons (1 : Matrix (Fin 2) (Fin 2) R) A
  let f : (∀ i, Fin (n i)) ↪ (∀ i, Fin (Fin.cons (α := fun _ => ℕ) 2 n i)) :=
    ⟨fun x => Fin.cons (0 : Fin 2) x, by
      intro x y h
      funext i
      exact congrFun h i.succ⟩
  have hAB : (gridTensor B).submatrix f f = gridTensor A := by
    ext x y
    change (∏ i, B i (f x i) (f y i)) = ∏ i, A i (x i) (y i)
    rw [Fin.prod_univ_succ]
    change (1 : Matrix (Fin 2) (Fin 2) R) 0 0 * (∏ i, A i (x i) (y i)) = _
    simp
  refine ⟨B, ?_⟩
  rw [← hAB]
  exact (complexity_le_iff ..).mpr ((realizableAtMost_complexity _).submatrix f f)

/-- A bound for paired widths `4 ≤ b ≤ d²` gives a bound for every tuple
of local widths `2 ≤ n ≤ d`. Padding an odd tuple at most doubles its volume. -/
theorem boundedGridTensorEstimate_of_paired {d : ℕ} {β C : ℝ} (hd : 2 ≤ d)
    (hβ : 0 ≤ β) (hC : 0 ≤ C) (hp : BoundedGridTensorEstimate R 4 (d^2) β C) :
    BoundedGridTensorEstimate R 2 d β (2*C) := by
  intro k n hn A
  let m := (k+1)/2
  have hm : m ≤ k := by dsimp [m]; omega
  have hw : (1 + (m : ℝ))^β ≤ (1 + (k : ℝ))^β :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_left hm 1) hβ
  by_cases he : k = m+m
  · have hpair : (complexity (gridTensor A) : ℝ) ≤
        C * (↑(∏ i, n i) : ℝ) * (1 + (m : ℝ))^β := pairedGrid_bound hp he n hn A
    apply hpair.trans
    gcongr
    linarith
  · have ho : k+1 = m+m := by dsimp [m] at he ⊢; omega
    obtain ⟨B, hB⟩ := padBinaryGrid n A
    have hpad (i : Fin (k+1)) : 2 ≤ Fin.cons (α := fun _ => ℕ) 2 n i ∧ Fin.cons (α := fun _ => ℕ) 2 n i ≤ d := by
      exact Fin.cases ⟨le_rfl, hd⟩ (fun j => hn j) i
    have hpair : (complexity (gridTensor B) : ℝ) ≤
        C * (↑(∏ i, Fin.cons (α := fun _ => ℕ) 2 n i) : ℝ) * (1 + (m : ℝ))^β :=
      pairedGrid_bound hp ho _ hpad B
    apply (Nat.cast_le (α := ℝ) |>.mpr hB).trans (hpair.trans ?_)
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Nat.cast_mul, Nat.cast_ofNat]
    rw [show C * (2 * (↑(∏ i, n i) : ℝ)) = 2 * C * ↑(∏ i, n i) by ring]
    gcongr

end

end FiniteFourier
end LinearAlgebra
end OAI
