import OAI.Computability.BorderVNP.ParseBooleanNetwork
import OAI.Computability.BorderVNP.BitVolume

/-! # The physical degree and entry types of a Boolean verifier network -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatch.BooleanLayout

open VPVNP.BooleanTranscript
open scoped Classical

variable {X W J : Type} {s : ℕ} [Fintype X] [Fintype W] [Fintype J]
variable (c : Circuit (X ⊕ W) s) (weighted : J → W)

/-- Every wire carries a single bit and every physical site has degree at most three. -/
theorem trivalent : (layout c weighted).network.Trivalent := by
  refine ⟨fun _ => rfl, fun v => ?_⟩
  unfold Crossing.Network.bitDegree
  convert degree_bound c weighted v using 2
  ext e
  rcases e with i | ⟨e,b⟩
  · simp [Layout.incident]
  · cases b <;> simp [Layout.incident]

/-- There is one distinct physical site per designated weight. -/
def weightSite : J ↪ (layout c weighted).Site where
  toFun j := .inl (.inr (.inr (.inr j)))
  inj' := by intro i j h; simpa using h

/-- The unique occurrence wire at a unary weight site. -/
noncomputable def weightEdge (j : J) : (layout c weighted).Edge :=
  .inr ((layout c weighted).slots.symm ⟨.inr (.inr (.inr j)), (0 : Fin 1)⟩)

/-- The occurrence wire enters the weight site. -/
theorem weightEdge_dst (j : J) :
    (layout c weighted).network.dst (weightEdge c weighted j) = weightSite c weighted j := by
  simp [weightEdge, weightSite, Layout.network]
  rfl

variable {R : Type*} [CommSemiring R] (weight : J → Bool → R)

/-- The only value at a weighted site is its weight applied to its single incident bit. -/
theorem weight_table (j : J) (a p) :
    (layout c weighted).tables (factor c weight) (weightSite c weighted j) a p =
      weight j (a ⟨weightEdge c weighted j, Or.inr (weightEdge_dst c weighted j)⟩ 0) := rfl

/-- Every entry at every other physical vertex is zero or one. -/
theorem other_tables_zero_one (v : (layout c weighted).Site)
    (hv : ∀ j, v ≠ weightSite c weighted j) (a p) :
    (layout c weighted).tables (factor c weight) v a p = 0 ∨
      (layout c weighted).tables (factor c weight) v a p = 1 := by
  rcases v with t | (u | (i | u))
  · exact factor_zero_one c weight t (fun j h => hv j (congrArg Sum.inl h)) _
  · cases u with
    | inl x => simp only [Layout.tables]; split <;> simp
    | inr w => exact Or.inr rfl
  · rcases i with ⟨u,i⟩
    simp only [Layout.tables]
    split <;> simp
  · exact Or.inr rfl

end ParseBatch.BooleanLayout

end BorderVNP
end Computability
end OAI
