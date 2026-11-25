import OAI.Hierarchy.NonlinearAmplification
import OAI.Hierarchy.NonlinearLoopless
import OAI.Hierarchy.GrassmannKernelRecursion

namespace OAI
/-! # Common loopless expanders from the paired-fiber comparison -/

namespace Hierarchy.NonlinearExpanders

open Finset Matrix ThreeFlat.Expander
open HyperbolicObstruction Computability.VPVNP.SpectralGeometry
open scoped Classical

universe u v

/-- All targets share the graph, degree and Poincaré constant. Only the
lower bound on the logarithmic order is chosen after the constants. -/
theorem expanders_of_matched_partitions
    {m : ℕ} (hm : 2 ≤ m) {b : ℝ} (hb : 0 ≤ b) (hbm : b < m)
    {J : Type*} [Fintype J] [Nonempty J]
    {I : Type v} (X : I → Type u) [∀ i, MetricSpace (X i)] [∀ i, CompleteSpace (X i)]
    (cat : ∀ i, CATZero (X i))
    (partitions : ∀ k : ℕ, ∃ e f : J → Fin ((2^k)^m) ≃ Fin (2^k) × Fin ((2^k)^(m-1)),
      ∀ i (x : Fin ((2^k)^m) → X i), variance x ≤ b*pairedEnergy e f x) :
    ∃ (h : ℕ) (γ : ℝ), 0 < h ∧ 0 ≤ γ ∧
      ∀ n₀ : ℕ, ∃ n ≥ n₀, ∃ G : Graph n h, ∀ i, Bound (transition G.arcs h) (X i) γ := by
  obtain ⟨K,α,C,hK,hα,hαm,hC,kernels⟩ :=
    sparse_kernels_of_matched_partitions hm hb hbm X partitions
  have seg (i : I) : HasCATZeroSegments (X i) := by
    intro x y t ht ht'
    obtain ⟨g,_,h⟩ := cat i x y
    exact ⟨g t,fun z => h z t ⟨ht,ht'⟩⟩
  obtain ⟨h,γ,hh,hγ,graphs⟩ := amplify_sparse_kernels hm hK hα hαm hC X seg kernels
  refine ⟨4*h,96*(γ+1),by omega,by positivity,?_⟩
  intro n₀
  obtain ⟨n,hn,c,sym,reg,bound⟩ := graphs (max 1 n₀)
  obtain ⟨G,hG⟩ := exists_loopless_double hh ((le_max_left _ _).trans hn) hγ c sym reg
  exact ⟨n+1,by omega,G,fun i => hG (X i) (bound i)⟩

end Hierarchy.NonlinearExpanders

end OAI
