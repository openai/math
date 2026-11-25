import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.SimpleGraph.Diam

/-! Face moves and diameter of bounded simple rational polytopes. -/

noncomputable section

open Set Filter Module

namespace OAI.Geometry.Hirsch

section Faces

variable {Space : Type} [AddCommGroup Space] [Module ℝ Space]

structure IsFace (body face : Set Space) : Prop where
  convex : Convex ℝ face
  extreme : IsExtreme ℝ body face

def dim (face : Set Space) : ℕ := finrank ℝ (vectorSpan ℝ face)

def facets (body : Set Space) : Set (Set Space) :=
  {face | IsFace body face ∧ face.Nonempty ∧ dim face + 1 = dim body}

def Simple (body : Set Space) : Prop :=
  ∀ point ∈ body.extremePoints ℝ, {face ∈ facets body | point ∈ face}.ncard = dim body

structure System (Space : Type) [AddCommGroup Space] [Module ℝ Space] (Row : Type) where
  normal : Row → Space →ₗ[ℝ] ℝ
  rhs : Row → ℝ

namespace System

variable {Row : Type} (sys : System Space Row)

def body : Set Space := {point | ∀ row, sys.rhs row ≤ sys.normal row point}

end System
end Faces

section Graph

variable {Space Row : Type} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [FiniteDimensional ℝ Space]

abbrev Vertex (body : Set Space) := ↥(body.extremePoints ℝ)

def graph (body : Set Space) (moves : ℕ) : SimpleGraph (Vertex body) where
  Adj first last := first ≠ last ∧ ∃ face, IsFace body face ∧ dim face ≤ moves ∧
    first.val ∈ face ∧ last.val ∈ face
  symm := ⟨by rintro _ _ ⟨hn, face, hf, hd, hx, hy⟩; exact ⟨hn.symm, face, hf, hd, hy, hx⟩⟩
  loopless := ⟨fun _ hh => hh.1 rfl⟩

end Graph

structure Polytope where
  Space : Type
  [group : NormedAddCommGroup Space]
  [moduleSpace : NormedSpace ℝ Space]
  [finiteDim : FiniteDimensional ℝ Space]
  Coord : Type
  basis : Basis Coord ℝ Space
  Row : Type
  [finiteRow : Finite Row]
  sys : System Space Row
  rationalNormal : ∀ row coord, ∃ value : ℚ, sys.normal row (basis coord) = value
  rationalRhs : ∀ row, ∃ value : ℚ, sys.rhs row = value
  compact : IsCompact sys.body
  nonempty : sys.body.Nonempty

attribute [instance] Polytope.group Polytope.moduleSpace Polytope.finiteDim Polytope.finiteRow

namespace Polytope

variable (poly : Polytope)

abbrev body := poly.sys.body
abbrev V := Vertex poly.body
def dimension := dim poly.body
def facetCount := (facets poly.body).ncard
abbrev dist (moves : ℕ) := (graph poly.body moves).dist

structure Objective where
  lin : poly.Space →ₗ[ℝ] ℝ
  low : poly.V
  high : poly.V
  bounds : ∀ point ∈ poly.body, lin low.val ≤ lin point ∧ lin point ≤ lin high.val
  positive : lin low.val < lin high.val

def Objective.gap {poly : Polytope} (obj : poly.Objective) (first last : poly.V) : ℝ :=
  |obj.lin first.val - obj.lin last.val| / (obj.lin obj.high.val - obj.lin obj.low.val)

end Polytope

def Subpolynomial (seq : ℕ → ℕ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∀ᶠ n : ℕ in atTop, (seq n : ℝ) ≤ (n : ℝ) ^ eps

def Superpolynomial (seq : ℕ → ℕ) : Prop :=
  ∀ exponent : ℝ, ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ exponent ≤ (seq n : ℝ)

structure Example where
  poly : Polytope
  obj : poly.Objective

theorem main :
  ∀ moves : ℕ → ℕ, (∀ n, 0 < moves n) → Subpolynomial moves →
    ∃ family : ℕ → Example,
      (∀ᶠ n in atTop, let poly := (family n).poly
        Simple poly.body ∧ (graph poly.body 1).Connected ∧ poly.facetCount = n) ∧
      Subpolynomial (fun n => (family n).poly.dimension) ∧
      Superpolynomial (fun n => (family n).poly.dist (moves n)
        (family n).obj.high (family n).obj.low) ∧
      ∀ alpha : ℝ, 0 < alpha → alpha < 1 → ∀ exponent : ℝ, ∀ᶠ n : ℕ in atTop,
        ∀ first last : (family n).poly.V, (n : ℝ) ^ (-alpha) ≤ (family n).obj.gap first last →
          (n : ℝ) ^ exponent ≤ (family n).poly.dist (moves n) first last := by
  sorry

theorem theorem_1_1 (moves : ℕ → ℕ) (positive : ∀ n, 0 < moves n) (sub : Subpolynomial moves) :
    ∃ family : ℕ → Example,
      (∀ᶠ n in atTop, let poly := (family n).poly
        Simple poly.body ∧ (graph poly.body 1).Connected ∧ poly.facetCount = n) ∧
      Subpolynomial (fun n => (family n).poly.dimension) ∧
      Superpolynomial (fun n => (graph (family n).poly.body (moves n)).diam) ∧
      ∀ alpha : ℝ, 0 < alpha → alpha < 1 → ∀ exponent : ℝ, ∀ᶠ n : ℕ in atTop,
        ∀ first last : (family n).poly.V, (n : ℝ)^(-alpha) ≤ (family n).obj.gap first last →
          (n : ℝ)^exponent ≤ (family n).poly.dist (moves n) first last := by
  sorry

theorem superpolynomial_graph_diameter :
    ∃ family : ℕ → Polytope,
      (∀ᶠ n in atTop, Simple (family n).body ∧ (graph (family n).body 1).Connected ∧
        (family n).facetCount = n) ∧
      Subpolynomial (fun n => (family n).dimension) ∧
      Superpolynomial (fun n => (graph (family n).body 1).diam) := by
  sorry

theorem graph_diameter_beats_polynomials :
    ∃ family : ℕ → Polytope,
      (∀ᶠ n in atTop, Simple (family n).body ∧ (graph (family n).body 1).Connected ∧
        (family n).facetCount = n) ∧
      Subpolynomial (fun n => (family n).dimension) ∧
      ∀ p : Polynomial ℝ, ∀ᶠ n : ℕ in atTop, p.eval (n : ℝ) < (graph (family n).body 1).diam := by
  sorry

theorem not_polynomialHirsch :
  ¬ (∃ coeff power : ℕ, ∀ poly : Polytope, Simple poly.body → (graph poly.body 1).Connected →
    ∀ first last : poly.V, poly.dist 1 first last ≤ coeff * (poly.facetCount + 1) ^ power) := by
  sorry

theorem theorem_1_2 :
  ∀ a b : ℝ, 0 < a → 0 < b → ∃ c delta : ℝ, 0 < c ∧ 0 < delta ∧
    ∃ threshold : ℕ, ∀ d excess : ℕ, threshold ≤ min d excess →
      ∃ poly : Polytope, Simple poly.body ∧ (graph poly.body 1).Connected ∧
        poly.dimension = d ∧ poly.facetCount = d + excess ∧
        ∃ first last : poly.V,
          c * excess * min ((excess : ℝ) ^ a) ((d : ℝ) ^ b) ≤
            poly.dist ⌊((min d excess : ℕ) : ℝ) ^ delta⌋₊ first last := by
  sorry

end OAI.Geometry.Hirsch
