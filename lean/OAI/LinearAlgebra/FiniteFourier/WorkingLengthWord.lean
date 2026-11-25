import OAI.LinearAlgebra.FiniteFourier.FiberSynchronization
import OAI.LinearAlgebra.FiniteFourier.GoodGrid
import OAI.LinearAlgebra.FiniteFourier.WorkingGroup

/-! # Fourier words on products of coprime working factors

Good's CRT factorization equips the factors with primitive roots of the
individual orders. The synchronized tensor construction combines their
occupied words using workspace proportional to the full transform length.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped BigOperators Function

/-- An occupied word for a cyclic transform of pairwise coprime factor lengths. -/
theorem occupiedWord_geometricMatrix_goodGrid {ι : Type} [Fintype ι] [DecidableEq ι]
    {n : ι → ℕ} {K : Type*} [Field K] {q : K} {c d : ℕ} (hc : 0 < c)
    (hn : ∀ i, 2 ≤ n i) (hcop : Pairwise (Nat.Coprime on n))
    (hq : IsPrimitiveRoot q (∏ i, n i))
    (hsmall : ∀ i (z : K), IsPrimitiveRoot z (n i) →
      OccupiedWord (Fin ((c-1) * n i)) d (geometricMatrix (n i) z)) :
    OccupiedWord (Fin ((c-1) * (∏ i, n i))) (fiberDepthFactor c * d)
      (geometricMatrix (∏ i, n i) q) := by
  have hn' (i : ι) : 0 < n i := (by decide : 0 < 2).trans_le (hn i)
  obtain ⟨w, hw, he⟩ := good_fourier_grid hn' hcop hq
  rw [he]
  apply OccupiedWord.relabel (e := (goodGridCRT hn' hcop).symm)
  have ht := occupiedWord_gridTensor hc (P := fun i => Fin (n i))
    (fun i => by simpa using hn i) (W := fun i => Fin ((c-1) * n i))
    (fun i => by simp [Nat.mul_comm]) (fun i => hsmall i _ (hw i))
  have hcard := (Fintype.card_congr (goodGridCRT hn' hcop)).symm
  simp only [Fintype.card_fin] at hcard
  rw [hcard, Nat.mul_comm _ (c-1)] at ht
  exact ht

/-- The long transform for one axis of a working group, built from its short
factor transforms over any field carrying the required roots. -/
theorem WorkingGroup.length_fourier_word {K E : Type*} [Field K] [Field E]
    {ι : Type*} [Fintype ι] {a : ι → ℕ} {t d : ℕ} (w : WorkingGroup K a t) (i : ι)
    {q : E} (hq : IsPrimitiveRoot q (w.length i))
    (hshort : ∀ m ∈ (w.axes i).factors, ∀ z : E, IsPrimitiveRoot z m →
      OccupiedWord (Fin (13 * m)) d (geometricMatrix m z)) :
    OccupiedWord (Fin (13 * w.length i)) (fiberDepthFactor 14 * d)
      (geometricMatrix (w.length i) q) := by
  let F := (w.axes i).factors
  have hlen : (∏ f : F, f.val) = w.length i := Finset.prod_coe_sort F id
  rw [← hlen] at hq ⊢
  apply occupiedWord_geometricMatrix_goodGrid (c := 14) (n := fun f : F => f.val) (by decide)
    (fun f => (w.axes i).factor_ge f.val f.property) _ hq
  · exact fun f z hz => hshort f.val f.property z hz
  · intro f g hfg
    exact (w.axes i).pairwise f.property g.property (fun he => hfg (Subtype.ext he))

end FiniteFourier
end LinearAlgebra
end OAI
