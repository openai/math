import OAI.LinearAlgebra.SpectralBooks.SiteTensor.OneIndexRelocation
import OAI.LinearAlgebra.SpectralBooks.IndependentRelocation
import OAI.LinearAlgebra.SpectralBooks.MovingNode
import OAI.LinearAlgebra.SpectralBooks.CubeTable.CubeCost

/-! # The product endpoint bound for actual exterior splitting nodes

Updating one movable slot leaves all fixed auxiliary sites in place. The
single-index wire inequality therefore applies in every background placement.
Successive relocation gives the product law; its total mass one preserves
the offset for all auxiliary wires.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
section

theorem CubeTable.IsCoupling.cost_sub_const {r : ℕ} {π : CubeTable r} {t : Fin r → ℝ}
    (h : CubeTable.IsCoupling π t) (N : CubeTable r) (C : ℝ) :
    CubeTable.cost π (fun e => N e - C) = CubeTable.cost π N - C := by
  simp only [CubeTable.cost, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h.total, one_mul]

namespace SiteTensor.Relocation
variable {r : ℕ} {q : Fin r → ℕ} {J : Type} {K : Type*}

theorem MovingTensor.placement_update (s : MovingTensor J K q) (p : Fin r → J) (i : Fin r) (v : J) :
    s.placement (Function.update p i v) = Function.update (s.placement p) (s.mark i) v := by
  funext k
  by_cases hk : k = s.mark i
  · subst k
    simp
  · rw [Function.update_of_ne hk]
    exact congrFun (s.background_update_same i p v) ⟨k,hk⟩

variable [Fintype J] [Nonempty J] [Field K]

/-- Every actual tensor node, with all auxiliary indices fixed, satisfies the
product Bernoulli endpoint estimate. -/
theorem MovingTensor.rawLogPrice_independent (s : MovingTensor J K q)
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
    (c : ℝ) (hc : 0 ≤ c) (a b z : Fin r → J) (t : Fin r → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc 0 1)
    (hza : ∀ i, rawWireDistance φ c (z i) (a i) = t i * rawWireDistance φ c (a i) (b i))
    (hzb : ∀ i, rawWireDistance φ c (z i) (b i) = (1-t i) * rawWireDistance φ c (a i) (b i)) :
    rawLogPrice φ c (s.grouped z) ≤ CubeTable.cost (CubeTable.independent t)
      (fun e => rawLogPrice φ c (s.grouped (fun i => if e i then b i else a i))) := by
  apply independent_relocation_cube (fun p => rawLogPrice φ c (s.grouped p)) a b z t ht
  intro i p
  simpa only [MovingTensor.grouped, s.placement_update] using
    rawLogPrice_relocate φ c hc s.T (s.placement p) (s.mark i) (a i) (z i) (b i)
      (t i) (ht i) (hza i) (hzb i)

/-- The product endpoint bound holds for prices corrected by the actual node's
accumulated exterior-wire costs. -/
theorem movingNodePrice_independent (x : MovingNode J K q)
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
    (c : ℝ) (hc : 0 ≤ c) (a b z : Fin r → J) (t : Fin r → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc 0 1)
    (hza : ∀ i, rawWireDistance φ c (z i) (a i) = t i * rawWireDistance φ c (a i) (b i))
    (hzb : ∀ i, rawWireDistance φ c (z i) (b i) = (1-t i) * rawWireDistance φ c (a i) (b i)) :
    movingNodePrice φ c x z ≤ CubeTable.cost (CubeTable.independent t)
      (fun e => movingNodePrice φ c x (cornerAt a b e)) := by
  unfold movingNodePrice
  rw [(CubeTable.independent_isCoupling ht).cost_sub_const]
  exact sub_le_sub_right (x.1.val.rawLogPrice_independent φ c hc a b z t ht hza hzb) _

end SiteTensor.Relocation
end

end

end SpectralBooks
end LinearAlgebra
end OAI
