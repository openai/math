import OAI.LinearAlgebra.SpectralBooks.TensorSemiring
import OAI.LinearAlgebra.SpectralBooks.Spectrum

/-! # Prices of tensors placed in a metric space

Each tensor has one finite-dimensional coordinate space per index. A map of the
indices groups all factors in each fiber at one site, including the scalar slot
of an empty fiber. Thus prices indexed by arbitrary lists of sites also handle
collisions, relabelings and insertion of trivial slots.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical
section

namespace SiteTensor.Raw

variable {I J K : Type*} [Fintype I]

/-- Group the local coordinates over the fibers of a placement. -/
def group (T : SiteTensor.Raw I K) (σ : I → J) : SiteTensor.Raw J K where
  Leg := fun j => (i : {i : I // σ i = j}) → T.Leg i.1
  finiteLeg := fun _ => inferInstance
  coeff := fun x => T.coeff (fun i => x (σ i) ⟨i, rfl⟩)

/-- Grouping sites preserves the underlying array of coefficients up to a bijection. -/
theorem group_ne_zero_iff [Zero K] (T : SiteTensor.Raw I K) (σ : I → J) :
    (T.group σ).coeff ≠ 0 ↔ T.coeff ≠ 0 := by
  constructor
  · intro h hzero
    exact h (funext fun x => congrFun hzero _)
  · intro h hzero
    apply h
    exact funext fun x => congrFun hzero (fun _ i => x i.1)

end SiteTensor.Raw

open SiteTensor

/-- Prices of finite nonzero placed tensors over a fixed field, with the price at
the zero tensor extended by zero. The normalization is the price of the binary
diagonal on the occupied sites. The transport and diameter bounds are the
corresponding estimates in the manuscript's preliminaries. -/
structure SpectralPlacementPrices (K : Type*) [Field K] (X : Type*) [PseudoMetricSpace X] where
  price {I : Type} [Fintype I] (T : Raw.{0} I K) (x : I → X) : ℝ
  zero_tensor {I : Type} [Fintype I] (T : Raw.{0} I K) (h : T.coeff = 0) (x : I → X) :
    price T x = 0
  collapsed {I : Type} [Fintype I] (T : Raw.{0} I K) (p : X) : price T (fun _ => p) = 0
  group {I J : Type} [Fintype I] [Fintype J] (T : Raw.{0} I K) (σ : I → J) (x : J → X) :
    price T (x ∘ σ) = price (T.group σ) x
  wire (x : Fin 2 → X) : price (Raw.diagonal (Fin 2) K (Fin 2)) x = dist (x 0) (x 1)
  transport {I : Type} [Fintype I] (T : Raw.{0} I K) (x y : I → X) :
    dist (price T x) (price T y) ≤ ∑ i, dist (x i) (y i) * Real.logb 2 (Fintype.card (T.Leg i))
  dist_le_diagonal {I : Type} [Fintype I] (x : I → X) (i j : I) :
    dist (x i) (x j) ≤ price (Raw.diagonal I K (Fin 2)) x
  normalized {I : Type} [Fintype I] [Nontrivial I] (x : I ↪ X) :
    ∃ φ : normalizedSpectrum (fun a b : TensorClass.{0} I K => a ≤ b), ∀ T : Raw.{0} I K,
      T.coeff ≠ 0 → price T x =
        price (Raw.diagonal I K (Fin 2)) x * Real.logb 2 (φ.val (ofRaw T) : ℝ)

namespace SpectralPlacementPrices

variable {K X : Type*} [Field K] [PseudoMetricSpace X]

/-- Restrict all tensor prices to an isometrically embedded metric subspace. -/
def pullback {Y : Type*} [MetricSpace Y] (P : SpectralPlacementPrices K X) (f : Y → X)
    (hf : Isometry f) : SpectralPlacementPrices K Y where
  price T x := P.price T (f ∘ x)
  zero_tensor T h x := P.zero_tensor T h (f ∘ x)
  collapsed T p := P.collapsed T (f p)
  group T σ x := P.group T σ (f ∘ x)
  wire x := (P.wire (f ∘ x)).trans (hf.dist_eq (x 0) (x 1))
  transport T x y := by simpa only [Function.comp_apply, hf.dist_eq] using P.transport T (f ∘ x) (f ∘ y)
  dist_le_diagonal x i j := by simpa only [Function.comp_apply, hf.dist_eq] using P.dist_le_diagonal (f ∘ x) i j
  normalized x := P.normalized (x.trans ⟨f, hf.injective⟩)

/-- On an injective placement with at least two sites the diagonal normalization
is strictly positive. -/
theorem diagonal_pos {Y : Type*} [MetricSpace Y] (P : SpectralPlacementPrices K Y)
    {I : Type} [Fintype I] [Nontrivial I] (x : I ↪ Y) :
    0 < P.price (Raw.diagonal I K (Fin 2)) x := by
  obtain ⟨i, j, hne⟩ := exists_pair_ne I
  exact (dist_pos.mpr (x.injective.ne hne)).trans_le (P.dist_le_diagonal x i j)

/-- For any map to a fixed finite set of distinct sites, a single spectral
point computes the prices of every tensor after its indices are grouped at
those sites. The number of tensor indices and their multiplicities can vary. -/
theorem normalized_group {Y : Type*} [MetricSpace Y] (P : SpectralPlacementPrices K Y)
    {J : Type} [Fintype J] [Nontrivial J] (y : J ↪ Y) :
    ∃ φ : normalizedSpectrum (fun a b : TensorClass.{0} J K => a ≤ b),
      0 < P.price (Raw.diagonal J K (Fin 2)) y ∧
      ∀ {I : Type} [Fintype I] (σ : I → J) (T : Raw.{0} I K), T.coeff ≠ 0 →
        P.price T (y ∘ σ) = P.price (Raw.diagonal J K (Fin 2)) y *
          Real.logb 2 (φ.val (ofRaw (T.group σ)) : ℝ) := by
  obtain ⟨φ, hφ⟩ := P.normalized y
  refine ⟨φ, P.diagonal_pos y, ?_⟩
  intro I _ σ T hT
  exact (P.group T σ y).trans (hφ _ ((T.group_ne_zero_iff σ).2 hT))

end SpectralPlacementPrices

end

end

end SpectralBooks
end LinearAlgebra
end OAI
