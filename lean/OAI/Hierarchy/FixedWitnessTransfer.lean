import OAI.Hierarchy.DegreeBorderProjection
import OAI.Hierarchy.GraphMonomials
import OAI.Computability.VPVNP.PolynomialBounds

namespace OAI
/-! # Transfer from fixed graph exponents to growing graph families

The host is indexed by its edge dimension. A fixed witness graph with an
arbitrarily large exponent eventually embeds in the growing hosts. The
polynomial loss in extracting a component is independent of this witness.
-/

namespace Hierarchy

open Computability.VPVNP MvPolynomial

abbrev SizeModel (K : Type*) [Field K] :=
  (σ : Type) → [Fintype σ] → ℕ → MvPolynomial σ K → Prop

variable {F : Type*} [Field F]

def GraphBorderAtMost (model : SizeModel (AlgebraicClosure F)) (G : IncidenceGraph)
    (n s : ℕ) : Prop :=
  DegreeBorderAtMost (model (G.TableVar n)) (Fintype.card G.V) s (G.contraction F n)

/-- Every polynomial circuit-size bound is eventually bounded by a pure power, uniformly. -/
theorem eventually_le_pure_power {s : ℕ → ℕ} (hs : PolynomiallyBounded s) :
    ∃ k N : ℕ, ∀ n ≥ N, s n ≤ n ^ k := by
  obtain ⟨A, d, N, h⟩ := hs
  refine ⟨d + 1, max A N, fun n hn => ?_⟩
  calc
    s n ≤ A * n ^ d := h n ((le_max_right ..).trans hn)
    _ ≤ n * n ^ d := Nat.mul_le_mul_right _ ((le_max_left ..).trans hn)
    _ = n ^ (d + 1) := by rw [pow_succ, Nat.mul_comm]

/-- A family of actual projections and an exact homogeneous-component simulation
give the stated degree-component border bound on each smaller graph. -/
theorem project_graph_border {model : SizeModel (AlgebraicClosure F)} {G H : IncidenceGraph}
    (n s t : ℕ) (φ : Projection F (G.TableVar n) (H.TableVar n))
    (specializes : φ.hom (G.contraction F n) = H.contraction F n)
    (simulation : ∀ g, model (G.TableVar n) s g → model (H.TableVar n) t
      ((Computability.BorderVNP.castProjection (algebraMap F (AlgebraicClosure F)) φ).hom
        (homogeneousComponent (Fintype.card G.V) g)))
    (host : GraphBorderAtMost model G n s) : GraphBorderAtMost model H n t := by
  rw [GraphBorderAtMost, ← specializes]
  exact DegreeBorderAtMost.projection φ (G.contraction_isHomogeneous F) host simulation

/-- Every polynomial host budget fails at all sufficiently large lengths when
the cost of specializing each host is bounded by the same polynomial. -/
theorem eventually_hard_of_fixed_witnesses
    (model : SizeModel (AlgebraicClosure F)) (host witness : ℕ → IncidenceGraph)
    (mono : ∀ (G : IncidenceGraph) n s t, s ≤ t →
      GraphBorderAtMost model G n s → GraphBorderAtMost model G n t)
    (cost : ℕ → ℕ → ℕ)
    (poly : ∀ s : ℕ → ℕ, PolynomiallyBounded s → PolynomiallyBounded (fun n => cost n (s n)))
    (transfer : ∀ h, ∃ N, ∀ n ≥ N, ∀ s, GraphBorderAtMost model (host n) n s →
      GraphBorderAtMost model (witness h) n (cost n s))
    (hard : ∀ k : ℕ, ∃ h N, ∀ n ≥ N, ¬ GraphBorderAtMost model (witness h) n (n ^ k))
    (s : ℕ → ℕ) (hs : PolynomiallyBounded s) :
    ∃ N, ∀ n ≥ N, ¬ GraphBorderAtMost model (host n) n (s n) := by
  obtain ⟨k, N₀, bound⟩ := eventually_le_pure_power (poly s hs)
  obtain ⟨h, N₁, large⟩ := hard k
  obtain ⟨N₂, restrict⟩ := transfer h
  refine ⟨max N₀ (max N₁ N₂), ?_⟩
  intro n hn small
  have h₀ : N₀ ≤ n := (le_max_left ..).trans hn
  have h₁ : N₁ ≤ n := (le_max_left ..).trans ((le_max_right ..).trans hn)
  have h₂ : N₂ ≤ n := (le_max_right ..).trans ((le_max_right ..).trans hn)
  exact large n h₁ (mono _ n _ _ (bound n h₀) (restrict n h₂ (s n) small))

end Hierarchy

end OAI
