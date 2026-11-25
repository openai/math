import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Finset.SDiff

namespace OAI
/-! # Slot-set transitions and root-to-leaf walks -/

namespace Hierarchy.FormulaPartition
open scoped BigOperators Classical
noncomputable section

variable (V : Type) (τ : V → Type) (F : Type*) [Field F] [DecidableEq V]

/-- A transition follows one child of a parse. Its factor uses precisely the
variables assigned to slots emitted by the sibling, which the path leaves behind. -/
structure Kernel where
  value : (∀ v, τ v) → Finset V → Finset V → F
  subset : ∀ a S T, value a S T ≠ 0 → T ⊆ S
  heavy : ∀ a S T, value a S T ≠ 0 → S.card ≤ 2*T.card
  locality : ∀ a b S T, (∀ v ∈ S \ T, a v = b v) → value a S T = value b S T

/-- A leaf supplies a single variable or a scalar. -/
structure Leaf where
  value : (∀ v, τ v) → Finset V → F
  small : ∀ a S, value a S ≠ 0 → S.card ≤ 1
  locality : ∀ a b S, (∀ v ∈ S, a v = b v) → value a S = value b S

variable {V τ F} [Fintype V]

def Kernel.act (k : Kernel V τ F) (a : ∀v,τ v) (f : Finset V → F) (S : Finset V) : F :=
  ∑ T : Finset V, k.value a S T * f T

def run (a : ∀v,τ v) (tip : Leaf V τ F) : List (Kernel V τ F) → Finset V → F
  | [] => tip.value a
  | k :: ks => k.act a (run a tip ks)

end
end Hierarchy.FormulaPartition

end OAI
