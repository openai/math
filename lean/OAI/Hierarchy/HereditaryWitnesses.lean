import OAI.Hierarchy.FixedWitnessTransfer
import OAI.Hierarchy.WitnessSubgraphs

namespace OAI
/-! # Fitting each fixed path and tree inside the explicit witness family -/

namespace Hierarchy

open Computability.VPVNP MvPolynomial

variable {F : Type*} [Field F]

/-- Polynomial overhead for specializing a homogeneous polynomial in a bounded
model, with the simulation checked on all exact outputs in the closure field. -/
structure ComponentSimulation (K : Type*) [Field K] (model : SizeModel K) where
  cost : ℕ → ℕ → ℕ
  polynomial : ∀ D s : ℕ → ℕ, PolynomiallyBounded D → PolynomiallyBounded s →
    PolynomiallyBounded (fun n => cost (D n) (s n))
  project : ∀ {σ τ : Type} [Fintype σ] [Fintype τ] (D s : ℕ)
    (φ : Projection K σ τ) (g : MvPolynomial σ K), model σ s g →
    model τ (cost D s) (φ.hom (homogeneousComponent D g))

/-- A host family containing every fixed witness for all sufficiently large
state counts cannot have polynomial border size if its fixed witnesses have
arbitrarily large eventual exponents. -/
theorem eventually_hard_of_subgraphs
    (model : SizeModel (AlgebraicClosure F)) (sim : ComponentSimulation _ model)
    (monotone : ∀ {σ : Type} [Fintype σ] {s t}, s ≤ t → ∀ g, model σ s g → model σ t g)
    (host witness : ℕ → IncidenceGraph)
    (order : PolynomiallyBounded (fun n => Fintype.card (host n).V))
    (embeds : ∀ h, ∃ N : ℕ, ∀ n ≥ N, Nonempty ((witness h).Embedding (host n)))
    (hard : ∀ k : ℕ, ∃ h N, ∀ n ≥ N, ¬ GraphBorderAtMost model (witness h) n (n ^ k))
    (s : ℕ → ℕ) (hs : PolynomiallyBounded s) :
    ∃ N, ∀ n ≥ N, ¬ GraphBorderAtMost model (host n) n (s n) := by
  apply eventually_hard_of_fixed_witnesses model host witness _
    (fun n s => sim.cost (Fintype.card (host n).V) s) _ _ hard s hs
  · intro G n s t le hs
    exact hs.mono (monotone le)
  · intro s hs
    exact sim.polynomial _ s order hs
  · intro h
    obtain ⟨N, inc⟩ := embeds h
    refine ⟨max N 1, ?_⟩
    intro n hn s hs
    obtain ⟨j⟩ := inc n ((le_max_left ..).trans hn)
    let base : Fin n := ⟨0, (le_max_right ..).trans hn⟩
    exact project_graph_border n s _ (j.projection F base) (j.hom_contraction F base)
      (sim.project _ s _) hs

theorem eventually_contains_path (h : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, Nonempty ((IncidenceGraph.path h).Embedding (IncidenceGraph.path n)) :=
  ⟨h, fun _ hn => ⟨IncidenceGraph.pathEmbedding hn⟩⟩

theorem eventually_contains_binaryTree (h : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, Nonempty ((BinaryTree.graph h).Embedding (BinaryTree.graph (Nat.log 2 n))) := by
  refine ⟨2 ^ h, fun n hn => ⟨BinaryTree.subtreeEmbedding ?_⟩⟩
  have hn' : n ≠ 0 := Nat.ne_of_gt ((Nat.pow_pos (by decide : 0 < 2)).trans_le hn)
  exact (Nat.le_log_iff_pow_le (by decide) hn').mpr hn

end Hierarchy

end OAI
