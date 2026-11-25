import OAI.LinearAlgebra.SpectralBooks.PlacedCoupledRelocation

/-! # Joint convexity for a finite family of marked indices

The endpoint law below is specified by its nonnegative masses and its
one-index marginals. This formulation permits any finite type of index names.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open scoped Classical

namespace SpectralPlacementPrices
open SiteTensor Relocation

/-- Joint convexity of placement, in the probability-law form of
Proposition 2.5. A fixed index is represented by equal endpoint positions. -/
theorem joint_convexity {K X : Type*} [Field K] [MetricSpace X] (P : SpectralPlacementPrices K X)
    {I : Type} [Fintype I] (T : Raw.{0} I K) (a z b : I → X) (t : I → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc 0 1)
    (hza : ∀ i, dist (z i) (a i) = t i * dist (a i) (b i))
    (hzb : ∀ i, dist (z i) (b i) = (1-t i) * dist (a i) (b i))
    (μ : (I → Bool) → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hmass : ∑ x, μ x = 1)
    (hmarg : ∀ i, (∑ x, if x i then μ x else 0) = t i) :
    P.price T z ≤ ∑ x : I → Bool, μ x * P.price T (fun i => if x i then b i else a i) := by
  let e := Fintype.equivFin I
  let f := e.arrowCongr (Equiv.refl Bool)
  let V := T.group e
  let π : CubeTable (Fintype.card I) := fun v => μ (f.symm v)
  have he (p : I → X) : P.price T p = P.price V (p ∘ e.symm) := by
    simpa [V, Function.comp_def] using P.group T e (p ∘ e.symm)
  have hπ : CubeTable.IsCoupling π (t ∘ e.symm) := by
    refine ⟨fun v => hμ (f.symm v), ?_, ?_⟩
    · exact (f.symm.sum_comp μ).trans hmass
    · intro j
      refine Eq.trans ?_ (hmarg (e.symm j))
      refine Fintype.sum_equiv f.symm _ _ fun x => ?_
      have hx : f.symm x (e.symm j) = x j := by simp [f, Equiv.arrowCongr]
      simp only [hx, π]
  have h := P.price_coupled_relocation V (a ∘ e.symm) (z ∘ e.symm) (b ∘ e.symm) (t ∘ e.symm)
    (fun j => ht (e.symm j)) (fun j => hza (e.symm j)) (fun j => hzb (e.symm j)) π hπ
  rw [he z]
  refine h.trans_eq ?_
  unfold CubeTable.cost
  refine Fintype.sum_equiv f.symm _ _ fun v => ?_
  rw [he]
  apply congrArg (μ (f.symm v) * ·)
  apply congrArg (P.price V)
  funext j
  have hx : f.symm v (e.symm j) = v j := by simp [f, Equiv.arrowCongr]
  simp only [Function.comp_apply, hx]

end SpectralPlacementPrices

end

end SpectralBooks
end LinearAlgebra
end OAI
