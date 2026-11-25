import OAI.LinearAlgebra.SpectralBooks.StretchProducts
import OAI.LinearAlgebra.SpectralBooks.StretchPriceUpper

/-! # Diagonals and private vectors at a collapsed placement

At a grouped site a single linear map can multiply by the indicator of
agreement with its central label. Any nonzero private vector at that site
is mutually obtainable with the scalar unit.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open MatrixMultiplication.Foundation
open scoped Classical
section
open PermutationStretch

variable {K : Type*} [Field K] {B C : Type} [Fintype B] [Fintype C]

private def weightedRead {I J : Type} (read : J → I) (weight : J → K) :
    (I → K) →ₗ[K] (J → K) where
  toFun f := fun j => weight j * f (read j)
  map_add' := by intros; ext; simp [mul_add]
  map_smul' := by intros; ext; simp [mul_left_comm]

/-- On nonzero scalar units product additivity forces the price to vanish. -/
theorem SitePriceEval.value_unit_eq_zero (p : SitePriceEval K B C) (hmul : p.BinaryProductAdditive) :
    p.value (fun (_ : Unit) (_ : B → Unit) (_ : C → Unit) => (1 : K)) = 0 := by
  let T : Tensor K Unit (B → Unit) (C → Unit) := fun _ _ _ => 1
  have hn : T ≠ 0 := by
    intro hz
    exact one_ne_zero (congrFun (congrFun (congrFun hz ()) (fun _ => ())) (fun _ => ()))
  have h : p.value T = p.value (SitePriceEval.splitProduct T T) := by
    apply p.value_reindex (Equiv.prodPUnit Unit).symm (fun _ => (Equiv.prodPUnit Unit).symm)
      (fun _ => (Equiv.prodPUnit Unit).symm)
    intros
    simp [T, SitePriceEval.splitProduct]
  rw [hmul T T hn hn] at h
  change p.value T = 0
  linarith

/-- In a placement grouping the common site with `C`, the full diagonal
has the price of the `B` diagonal. -/
theorem SitePriceEval.MonoGroupedC.value_diagAll_eq_diagB {p : SitePriceEval K B C}
    (hg : p.MonoGroupedC) (W : Type) [Fintype W] :
    p.value (diagAll (K := K) B C W) = p.value (diagB (K := K) B C W) := by
  apply le_antisymm
  · let A := weightedRead (fun (z : W × (C → W)) => (z.1, (fun _ : C => ())))
        (fun z => diagonalCoeff (K := K) z.1 z.2)
    convert hg (diagB (K := K) B C W) A using 2
    funext v x y
    simp [A, weightedRead, diagAll, diagB, placeB, mul_comm]
  · let A := LinearMap.funLeft K K (fun (z : W × (C → Unit)) => (z.1, (fun _ : C => z.1)))
    convert hg (diagAll (K := K) B C W) A using 2
    funext v x y
    simp [A, diagAll, diagB, placeB, diagonalCoeff]

/-- In a placement grouping the common site with `B`, the full diagonal
has the price of the `C` diagonal. -/
theorem SitePriceEval.MonoGroupedB.value_diagAll_eq_diagC {p : SitePriceEval K B C}
    (hg : p.MonoGroupedB) (W : Type) [Fintype W] :
    p.value (diagAll (K := K) B C W) = p.value (diagC (K := K) B C W) := by
  apply le_antisymm
  · let A := weightedRead (fun (z : W × (B → W)) => (z.1, (fun _ : B => ())))
        (fun z => diagonalCoeff (K := K) z.1 z.2)
    convert hg (diagC (K := K) B C W) A using 2
    rfl
  · let A := LinearMap.funLeft K K (fun (z : W × (B → Unit)) => (z.1, (fun _ : B => z.1)))
    convert hg (diagAll (K := K) B C W) A using 2
    funext v x y
    simp [A, diagAll, diagC, placeC, diagonalCoeff]

/-- A nonzero tensor private to the grouped `C` side is a vector at that site. -/
theorem SitePriceEval.MonoGroupedC.value_placeC_eq_zero {p : SitePriceEval K B C}
    (hg : p.MonoGroupedC) (hmul : p.BinaryProductAdditive)
    {U : Type} {Y : C → Type} [Fintype U] [∀ i, Fintype (Y i)]
    (Q : U → (∀ i, Y i) → K) (hQ : Q ≠ 0) : p.value (placeC B Q) = 0 := by
  let T : Tensor K Unit (B → Unit) (C → Unit) := fun _ _ _ => 1
  rw [← p.value_unit_eq_zero hmul]
  change p.value (placeC B Q) = p.value T
  apply le_antisymm
  · let A := weightedRead (fun _ : U × (∀ c, Y c) => ((), (fun _ : C => ())))
        (fun z => Q z.1 z.2)
    convert hg T A using 2
    funext v x y
    simp [A, weightedRead, T, placeC]
  · obtain ⟨u, y, hy⟩ : ∃ u y, Q u y ≠ 0 := by
      by_contra! hh
      exact hQ (funext fun u => funext (hh u))
    let A := weightedRead (fun _ : Unit × (C → Unit) => (u, y)) (fun _ => (Q u y)⁻¹)
    convert hg (placeC B Q) A using 2
    funext v x y
    simp [A, weightedRead, T, placeC, hy]

/-- A nonzero tensor private to the grouped `B` side is a vector at that site. -/
theorem SitePriceEval.MonoGroupedB.value_placeB_eq_zero {p : SitePriceEval K B C}
    (hg : p.MonoGroupedB) (hmul : p.BinaryProductAdditive)
    {U : Type} {X : B → Type} [Fintype U] [∀ i, Fintype (X i)]
    (P : U → (∀ i, X i) → K) (hP : P ≠ 0) : p.value (placeB C P) = 0 := by
  let T : Tensor K Unit (B → Unit) (C → Unit) := fun _ _ _ => 1
  rw [← p.value_unit_eq_zero hmul]
  change p.value (placeB C P) = p.value T
  apply le_antisymm
  · let A := weightedRead (fun _ : U × (∀ b, X b) => ((), (fun _ : B => ())))
        (fun z => P z.1 z.2)
    convert hg T A using 2
    funext v x y
    simp [A, weightedRead, T, placeB]
  · obtain ⟨u, x, hx⟩ : ∃ u x, P u x ≠ 0 := by
      by_contra! hh
      exact hP (funext fun u => funext (hh u))
    let A := weightedRead (fun _ : Unit × (B → Unit) => (u, x)) (fun _ => (P u x)⁻¹)
    convert hg (placeB C P) A using 2
    funext v x y
    simp [A, weightedRead, T, placeB, hx]

end

end

end SpectralBooks
end LinearAlgebra
end OAI
