import OAI.Hierarchy.DegreeBorder
import OAI.Hierarchy.GraphContractions
import OAI.Computability.BorderVNP.ModelBaseChange
import OAI.Computability.VPVNP.Classes

namespace OAI
/-! # Degree-component border bounds for arithmetic circuits -/

namespace Hierarchy

open Computability.BorderVNP MvPolynomial

variable {σ F E : Type*} [Field F] [Field E]

/-- A formal polynomial admits a circuit with at most the given number of operation gates. -/
abbrev HasCircuit (s : ℕ) (f : MvPolynomial σ F) : Prop := Computability.VPVNP.circuitSize f ≤ s

/-- The attainable coefficient vectors in the bounded circuit model used by `Computability.BorderVNP`. -/
theorem hasCircuit_image (d s : ℕ) :
    coeffVector d '' {f : MvPolynomial σ F | HasCircuit s f} = circuitImage F σ d s := by
  ext v
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨m, hm, c, rfl⟩ := Computability.VPVNP.circuitSize_le_iff.mp hf
    exact ⟨m, hm, c, rfl⟩
  · rintro ⟨m, hm, c, rfl⟩
    exact ⟨c.polynomial, (Computability.VPVNP.circuitSize_le_of_circuit c).trans hm, rfl⟩

theorem circuitDegreeBorder_iff_borderApprox (d s : ℕ) (p : MvPolynomial σ F) :
    DegreeBorderAtMost HasCircuit d s p ↔ Computability.BorderVNP.BorderApprox d s p := by
  simp only [DegreeBorderAtMost, degreeModelClosure, hasCircuit_image, BorderApprox, geometricApprox]

/-- A field extension preserves every degree-component circuit border bound. -/
theorem circuitDegreeBorder_map_iff [Algebra F E] (d s : ℕ) (p : MvPolynomial σ F) :
    DegreeBorderAtMost HasCircuit d s (map (algebraMap F E) p) ↔ DegreeBorderAtMost HasCircuit d s p := by
  simpa only [circuitDegreeBorder_iff_borderApprox] using Computability.BorderVNP.borderApprox_map_iff (E := E) d s p

theorem HasCircuit.degreeBorderAtMost {d s : ℕ} {p : MvPolynomial σ F} (h : HasCircuit s p) :
    DegreeBorderAtMost HasCircuit d s p :=
  degreeBorderAtMost_of_exact_map ((Computability.VPVNP.circuitSize_map_le (algebraMap F (AlgebraicClosure F)) p).trans h)

/-- A VP family's circuit-size bound also bounds each degree component in the border model. -/
theorem isVP_hasPolynomialBorder {ι : ℕ → Type} [∀ n, Fintype (ι n)] {p : Computability.VPVNP.Family F ι}
    (h : Computability.VPVNP.IsVP p) (degree : ℕ → ℕ) :
    ∃ s : ℕ → ℕ, Computability.VPVNP.PolynomiallyBounded s ∧
      ∀ n, DegreeBorderAtMost HasCircuit (degree n) (s n) (p n) :=
  ⟨_, h.2, fun _ => HasCircuit.degreeBorderAtMost le_rfl⟩

namespace IncidenceGraph

theorem map_contraction {F K : Type*} [CommSemiring F] [CommSemiring K]
    (G : IncidenceGraph) (φ : F →+* K) (n : ℕ) :
    map φ (G.contraction F n) = G.contraction K n := by
  classical
  simp [contraction, assignmentMonomial, map_sum, map_prod]

/-- Independent-table contractions have the same circuit border bound under scalar extension. -/
theorem circuit_border_baseChange (G : IncidenceGraph) (F E : Type*) [Field F] [Field E] [Algebra F E]
    (q s : ℕ) :
    DegreeBorderAtMost HasCircuit (Fintype.card G.V) s (G.contraction E q) ↔
      DegreeBorderAtMost HasCircuit (Fintype.card G.V) s (G.contraction F q) := by
  simpa only [G.map_contraction] using
    circuitDegreeBorder_map_iff (E := E) (Fintype.card G.V) s (G.contraction F q)

end IncidenceGraph
end Hierarchy

end OAI
