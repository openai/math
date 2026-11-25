import OAI.LinearAlgebra.FiniteFourier.GeometricMatrix
import OAI.LinearAlgebra.FiniteFourier.LayerSynchronization
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Good's prime-factor factorization on a finite grid

Pairwise coprime cyclic lengths admit simultaneous CRT indexing. In these indices the
Fourier matrix is the grid tensor at the primitive factor roots. A common layer-word
depth for all factors therefore suffices for the full transform.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open Finset
open scoped Function

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [DecidableEq ι] in
private theorem modEq_gridProduct {x y : ℕ} (hc : Pairwise (Nat.Coprime on n))
    (h : ∀ i, x ≡ y [MOD n i]) : x ≡ y [MOD ∏ i, n i] := by
  rw [← Finset.prod_map_toList]
  apply (Nat.modEq_list_map_prod_iff _).mpr (fun i _ => h i)
  exact (Finset.nodup_toList _).pairwise_of_forall_ne (fun _ _ _ _ hij => hc hij)

/-- The residue coordinates of a cyclic index for any finite family of coprime factors. -/
def goodGridCRT (hn : ∀ i, 0 < n i) (hc : Pairwise (Nat.Coprime on n)) :
    Fin (∏ i, n i) ≃ ∀ i, Fin (n i) :=
  Equiv.ofBijective (fun x i => ⟨x.val % n i, Nat.mod_lt _ (hn i)⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro x y he
      apply Fin.ext
      exact (modEq_gridProduct hc (fun i => congrArg Fin.val (congrFun he i))).eq_of_lt_of_lt
        x.isLt y.isLt, by simp [Fintype.card_pi]⟩)

variable {K : Type*} [Field K] {q : K}

/-- After CRT indexing, a Fourier matrix of product order is a single grid tensor. -/
theorem good_fourier_grid (hn : ∀ i, 0 < n i) (hc : Pairwise (Nat.Coprime on n))
    (hq : IsPrimitiveRoot q (∏ i, n i)) :
    ∃ w : ι → K, (∀ i, IsPrimitiveRoot (w i) (n i)) ∧ geometricMatrix (∏ i, n i) q =
      (gridTensor (fun i => geometricMatrix (n i) (w i))).submatrix
        (goodGridCRT hn hc) (goodGridCRT hn hc) := by
  let e (i : ι) := Nat.chineseRemainderOfFinset (fun j => if i = j then 1 else 0) n
    univ (fun j _ => (hn j).ne') (hc.set_pairwise _)
  have he (i j : ι) : (e i).val ≡ (if i = j then 1 else 0) [MOD n j] :=
    (e i).property j (mem_univ _)
  refine ⟨fun i => q ^ (e i).val, ?_, ?_⟩
  · intro i
    constructor
    · rw [← pow_mul, hq.pow_eq_one_iff_dvd, ← Nat.modEq_zero_iff_dvd]
      apply modEq_gridProduct hc
      intro j
      by_cases hij : i = j
      · subst j
        exact (dvd_mul_left _ _).modEq_zero_nat
      · simpa [hij] using (he i j).mul_right (n i)
    · intro k hk
      rw [← pow_mul, hq.pow_eq_one_iff_dvd] at hk
      have hk' := ((dvd_prod_of_mem n (mem_univ i)).trans hk).modEq_zero_nat
      apply Nat.modEq_zero_iff_dvd.mp
      simpa using ((he i i).mul_right k).symm.trans hk'
  · ext x y
    simp only [Matrix.submatrix_apply, gridTensor, geometricMatrix_apply, ← pow_mul,
      Finset.prod_pow_eq_pow_sum]
    apply pow_eq_pow_of_modEq _ hq.pow_eq_one
    apply modEq_gridProduct hc
    intro j
    let p (i : ι) := (x.val % n i) * (y.val % n i)
    change x.val * y.val ≡ ∑ i, (e i).val * p i [MOD n j]
    have hsum : (∑ i, (e i).val * p i) ≡ ∑ i, (if i = j then 1 else 0) * p i [MOD n j] :=
      Nat.ModEq.sum fun i _ => (he i j).mul_right (p i)
    exact ((Nat.mod_modEq _ _).mul (Nat.mod_modEq _ _)).symm.trans
      (by simpa [ite_mul, p] using hsum.symm)

/-- Good's prime-factor transform has the same synchronized depth as its factors. -/
theorem layerWord_geometricMatrix_goodGrid {d : ℕ} (hn : ∀ i, 0 < n i)
    (hc : Pairwise (Nat.Coprime on n)) (hq : IsPrimitiveRoot q (∏ i, n i))
    (hsmall : ∀ i (z : K), IsPrimitiveRoot z (n i) → LayerWord d (geometricMatrix (n i) z)) :
    LayerWord d (geometricMatrix (∏ i, n i) q) := by
  obtain ⟨w, hw, he⟩ := good_fourier_grid hn hc hq
  rw [he]
  exact (layerWord_grid fun i => hsmall i _ (hw i)).relabel (goodGridCRT hn hc).symm

end

end

end FiniteFourier
end LinearAlgebra
end OAI
