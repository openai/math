import OAI.Hierarchy.GraphContractions
import OAI.Hierarchy.FlatPrices
import OAI.Hierarchy.ModelBorder

namespace OAI
/-! # The graph-family criterion of Low-degree VNP lower bounds, Theorem 6.1

These predicates give the family form of the graph classification used in the
arithmetic separation. Edge labels at length `n` range over `Fin n`. The
necessary bounds allow Zariski limits of unrestricted-degree computations.
The sufficient bounds give exact computations over the original field.
-/

namespace Hierarchy

open Computability.VPVNP

abbrev GraphFamily := ℕ → IncidenceGraph

namespace GraphFamily

def PolynomialOrder (G : GraphFamily) : Prop :=
  PolynomiallyBounded (fun n => Fintype.card (G n).V)

def BoundedDegree (G : GraphFamily) : Prop :=
  ∃ b, ∀ n (v : (G n).V), (G n).degree v ≤ b

def BoundedComponents (G : GraphFamily) : Prop :=
  ∃ b, ∀ n (v : (G n).V), ((G n).component v).card ≤ b

def BoundedCutwidth (G : GraphFamily) : Prop := ∃ b, ∀ n, (G n).CutwidthAtMost b

def BoundedTreewidth (G : GraphFamily) : Prop := ∃ b, ∀ n, (G n).TreewidthAtMost b

variable (G : GraphFamily) (F : Type*) [Field F]

/-- Each graph polynomial is homogeneous of degree equal to its number of vertices. -/
def PolynomialBorderFormula : Prop :=
  ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧ ∀ n, DegreeBorderAtMost HasFormula
    (Fintype.card (G n).V) (s n) ((G n).contraction F n)

def PolynomialBorderABP : Prop :=
  ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧ ∀ n, DegreeBorderAtMost HasABP
    (Fintype.card (G n).V) (s n) ((G n).contraction F n)

def PolynomialBorderCircuit : Prop :=
  ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧ ∀ n,
    DegreeBorderAtMost (fun t p => circuitSize p ≤ t)
      (Fintype.card (G n).V) (s n) ((G n).contraction F n)

theorem borderFormula_of_isVF (h : IsVF (contractionFamily F G)) : G.PolynomialBorderFormula F :=
  isVF_hasPolynomialBorder h (fun n => Fintype.card (G n).V)

theorem borderABP_of_isVBP (h : IsVBP (contractionFamily F G)) : G.PolynomialBorderABP F :=
  isVBP_hasPolynomialBorder h (fun n => Fintype.card (G n).V)

theorem borderCircuit_of_isVP (h : IsVP (contractionFamily F G)) : G.PolynomialBorderCircuit F :=
  ⟨_, h.2, fun n => degreeBorderAtMost_of_exact_map
    (circuitSize_map_le (algebraMap F (AlgebraicClosure F)) ((G n).contraction F n))⟩

end GraphFamily

/-- The exact algorithms in LD Theorem 6.1. -/
structure GraphUpperBounds (F : Type*) [Field F] : Prop where
  formula : ∀ G : GraphFamily, G.PolynomialOrder → G.BoundedDegree →
    G.BoundedComponents → IsVF (contractionFamily F G)
  abp : ∀ G : GraphFamily, G.PolynomialOrder → G.BoundedCutwidth →
    IsVBP (contractionFamily F G)
  circuit : ∀ G : GraphFamily, G.PolynomialOrder → G.BoundedDegree →
    G.BoundedTreewidth → IsVP (contractionFamily F G)

/-- The three lower bounds of LD Theorem 6.1 use the degree components of
approximating computations with scalars in the algebraic closure. -/
structure GraphBorderNecessity (F : Type*) [Field F] : Prop where
  formula : ∀ G : GraphFamily, G.PolynomialOrder → G.PolynomialBorderFormula F →
    G.BoundedComponents ∧ G.BoundedDegree
  abp : ∀ G : GraphFamily, G.PolynomialOrder → G.PolynomialBorderABP F → G.BoundedCutwidth
  circuit : ∀ G : GraphFamily, G.PolynomialOrder → G.PolynomialBorderCircuit F →
    G.BoundedTreewidth ∧ G.BoundedDegree

/-- The conditional graph classification, with separate geometric and arithmetic
statements. All bound constants are uniform in the family index. -/
def LowDegreeGraphTheorem (F : Type*) [Field F] : Prop :=
  AllHomogeneousFlats (AlgebraicClosure (⊥ : Subfield F)) → GraphUpperBounds F ∧ GraphBorderNecessity F

end Hierarchy

end OAI
