import OAI.LinearAlgebra.SpectralBooks.Fermion.Pascal
import OAI.Probability.SpanningForest.CauchyBinet

/-! # Cauchy–Binet factorization of the fermion Gram minors -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

open Finset Matrix

private theorem stateMinor_of_card (f : ℕ → ℕ → ℤ) {I J : Finset ℕ} {k : ℕ}
    (hI : I.card = k) (hJ : J.card = k) :
    stateMinor f I J =
      (Matrix.of fun i j : Fin k ↦ f (I.orderEmbOfFin hI i) (J.orderEmbOfFin hJ j)).det := by
  subst k
  rw [stateMinor, dite_eq_left hJ]

private theorem sum_powersetCard_fin_val {M : Type*} [AddCommMonoid M] (N k : ℕ)
    (F : Finset ℕ → M) :
    ∑ S ∈ (univ : Finset (Fin N)).powersetCard k, F (S.map Fin.valEmbedding) =
      ∑ S ∈ (range N).powersetCard k, F S := by
  rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_univ, powersetCard_map, sum_map]
  rfl

/-- Sorted column indices of a subset of `Fin N` agree with the sorted natural indices. -/
private theorem orderEmb_map_val {N k : ℕ} (S : Finset (Fin N)) (hS : S.card = k)
    (i : Fin k) :
    (S.orderEmbOfFin hS i : ℕ) =
      (S.map Fin.valEmbedding).orderEmbOfFin ((card_map _).trans hS) i := by
  apply congrFun (orderEmbOfFin_unique _ _ (Fin.val_strictMono.comp (S.orderEmbOfFin hS).strictMono))
  intro j
  exact mem_map.mpr ⟨_, S.orderEmbOfFin_mem hS j, rfl⟩

/-- The fully contracted binomial minor factors through the exterior Pascal matrix.
The cutoff can be chosen using the largest occupied mode of the left state alone. -/
theorem pascal_gram_minor {N : ℕ} {I J : Finset ℕ} (hI : I ⊆ range N) :
    stateMinor (fun i j ↦ ((i + j).choose i : ℤ)) I J =
      ∑ S ∈ (range N).powerset, pascalMinor I S * pascalMinor J S := by
  classical
  by_cases hJ : J.card = I.card
  · let A : Matrix (Fin I.card) (Fin N) ℤ :=
      Matrix.of fun i k ↦ ((I.orderEmbOfFin rfl i).choose k : ℤ)
    let B : Matrix (Fin I.card) (Fin N) ℤ :=
      Matrix.of fun j k ↦ ((J.orderEmbOfFin hJ j).choose k : ℤ)
    have hgram : stateMinor (fun i j ↦ ((i + j).choose i : ℤ)) I J = (A * B.transpose).det := by
      rw [stateMinor_of_card _ rfl hJ]
      congr 1
      ext i j
      change _ = ∑ k : Fin N, _
      exact ((Fin.sum_univ_eq_sum_range _ _).trans <|
        pascal_gram_entry (j := J.orderEmbOfFin hJ j) (mem_range.mp (hI (I.orderEmbOfFin_mem rfl i)))).symm
    rw [hgram, Problem336.CauchyBinet.det_mul_eq_sum_principal_minors, Fintype.card_fin]
    let F := fun S ↦ pascalMinor I S * pascalMinor J S
    calc
      _ = ∑ S ∈ (univ : Finset (Fin N)).powersetCard I.card, F (S.map Fin.valEmbedding) := by
        apply sum_congr rfl
        intro S hS
        have hc := (mem_powersetCard.mp hS).2
        let e := (S.orderIsoOfFin hc).toEquiv
        let col := fun i : Fin I.card ↦ S.orderEmbOfFin hc i
        have hA : (A.submatrix id col).det = pascalMinor I (S.map Fin.valEmbedding) := by
          rw [pascalMinor, stateMinor_of_card _ rfl ((card_map _).trans hc)]
          congr 1
          ext i j
          simp only [Matrix.submatrix_apply, Matrix.of_apply, id_eq, A, col, orderEmb_map_val]
        have hB : (B.submatrix id col).det = pascalMinor J (S.map Fin.valEmbedding) := by
          rw [pascalMinor, stateMinor_of_card _ hJ ((card_map _).trans hc)]
          congr 1
          ext i j
          simp only [Matrix.submatrix_apply, Matrix.of_apply, id_eq, B, col, orderEmb_map_val]
        rw [← Matrix.det_submatrix_equiv_self e]
        change ((B.transpose * A).submatrix col col).det = _
        rw [← Matrix.submatrix_mul_equiv B.transpose A col (Equiv.refl _) col, Matrix.det_mul]
        change ((B.submatrix id col).transpose).det * (A.submatrix id col).det = _
        rw [Matrix.det_transpose, hA, hB, mul_comm]
      _ = ∑ S ∈ (range N).powersetCard I.card, F S := sum_powersetCard_fin_val ..
      _ = _ := by
        apply sum_subset (by simp [powersetCard_eq_filter])
        intro S hS hout
        have hc : S.card ≠ I.card := fun h ↦ hout (mem_powersetCard.mpr ⟨mem_powerset.mp hS, h⟩)
        simp [F, pascalMinor, stateMinor, hc]
  · rw [stateMinor, dite_eq_right hJ]
    symm
    apply sum_eq_zero
    intro S _
    by_cases hS : S.card = I.card
    · have hSJ : S.card ≠ J.card := fun h ↦ hJ (h.symm.trans hS)
      simp [pascalMinor, stateMinor, hSJ]
    · simp [pascalMinor, stateMinor, hS]

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
