import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Joint
import OAI.LinearAlgebra.SpectralBooks.Prices

/-! # Joint convexity for arbitrary tensors placed in a spectral space

Group all endpoint and intermediate positions at one finite set of labels. A
single normalized point computes the prices of all tensors on these labels,
including the wires which determine their distances.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open scoped Classical
open Set

namespace SpectralPlacementPrices
open SiteTensor Relocation

variable {K X : Type*} [Field K] [MetricSpace X] (P : SpectralPlacementPrices K X)

/-- Coupled relocation of an arbitrary tensor over a field. The marginals may
differ between marks, and the endpoint choices may be dependent. -/
theorem price_coupled_relocation {r : ℕ} (T : Raw.{0} (Fin r) K) (a z b : Fin r → X)
    (t : Fin r → ℝ) (ht : ∀ i, t i ∈ Icc (0 : ℝ) 1)
    (hza : ∀ i, dist (z i) (a i) = t i * dist (a i) (b i))
    (hzb : ∀ i, dist (z i) (b i) = (1-t i) * dist (a i) (b i))
    (π : CubeTable r) (hπ : CubeTable.IsCoupling π t) :
    P.price T z ≤ CubeTable.cost π (fun x ↦ P.price T (fun i ↦ if x i then b i else a i)) := by
  rcases eq_or_ne r 0 with rfl | hr
  · have hc (x : Fin 0 → Bool) : (fun i ↦ if x i then b i else a i) = z := Subsingleton.elim _ _
    simp only [CubeTable.cost, hc, ← Finset.sum_mul, hπ.total, one_mul, le_rfl]
  let : NeZero r := ⟨hr⟩
  let points (v : Fin r × Fin 3) := ![a v.1, z v.1, b v.1] v.2
  let label (k : Fin 3) (i : Fin r) : Fin r × Fin 3 := (i,k)
  have his (x : Fin r → Bool) : (fun i ↦ if x i then b i else a i) = points ∘ cornerAt (label 0) (label 2) x := by
    funext i
    cases hx : x i <;> simp [cornerAt, hx, points, label]
  change P.price T (points ∘ label 1) ≤ _
  rcases P.zero_or_common_group_price points with hzero | ⟨φ,c,hc,hprice⟩
  · simp only [his, hzero, CubeTable.cost, mul_zero, Finset.sum_const_zero, le_rfl]
  · have hd (p q : Fin r × Fin 3) : rawWireDistance φ c p q = dist (points p) (points q) :=
      (hprice (Raw.diagonal (Fin 2) K (Fin 2)) ![p,q]).symm.trans (P.wire _)
    simp only [his, hprice]
    apply rawLogPrice_coupled_relocation φ c hc.le T (label 0) (label 1) (label 2) t ht _ _ π hπ
    · intro i
      rw [hd, hd]
      exact hza i
    · intro i
      rw [hd, hd]
      exact hzb i

/-- The synchronized endpoint coupling, with an arbitrary finite mark type. -/
theorem price_le_of_common_fraction {I : Type} [Fintype I] (T : Raw.{0} I K) (a z b : I → X)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hza : ∀ i, dist (z i) (a i) = t * dist (a i) (b i))
    (hzb : ∀ i, dist (z i) (b i) = (1-t) * dist (a i) (b i)) :
    P.price T z ≤ (1-t) * P.price T a + t * P.price T b := by
  let e := Fintype.equivFin I
  let V := T.group e
  have he (p : I → X) : P.price T p = P.price V (p ∘ e.symm) := by
    have hp : (p ∘ e.symm) ∘ e = p := by funext i; simp
    simpa only [hp, V] using P.group T e (p ∘ e.symm)
  let M : CubeTable (Fintype.card I) := fun u ↦ P.price V (fun i ↦ if u i then b (e.symm i) else a (e.symm i))
  have h := CubeTable.synchronized_of_forall_couplings (M := M) ht
    (P.price_coupled_relocation V (a ∘ e.symm) (z ∘ e.symm) (b ∘ e.symm) (fun _ ↦ t)
      (fun _ ↦ ht) (fun i ↦ hza (e.symm i)) (fun i ↦ hzb (e.symm i)))
  rw [he z, he a, he b]
  exact h

end SpectralPlacementPrices

end

end SpectralBooks
end LinearAlgebra
end OAI
