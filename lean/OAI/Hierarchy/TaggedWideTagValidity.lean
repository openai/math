import OAI.Hierarchy.TaggedData
import OAI.Hierarchy.TaggedWideHost

namespace OAI
/-! # One fixed width-one occurrence checks the parent tag word -/

noncomputable section
namespace Hierarchy.Tagged.WideHost
open ThreeFlat Routing
open scoped Classical BigOperators

/-- The two payload arrays use the same fixed word at every row. The tags
are read in their original row order. This check reuses existing wires and
has no arbitrary hidden choice even at width zero. -/
def permutationRead {V : Type*} {h : ℕ} (read : Row h × Fin h → V) :
    Fin (pins h h) → V := fun j =>
  match (portIndex h h).symm j with
  | .inl (_,b) => read (0,b)
  | .inr (.inl t) => read t
  | .inr (.inr (_,b)) => read (0,b)

theorem permutation_factor {F : Type*} {V : Type*} [Field F] {h : ℕ}
    (read : Row h × Fin h → V) (v : V → Bool) :
    coeff F h h (v ∘ permutationRead read) =
      if Function.Bijective (fun i : Row h =>
        (Computability.VPVNP.RAMSerialization.wordBits h).symm (fun b => v (read (i,b)))) then 1 else 0 := by
  classical
  have sourceEq (i : Row h) : source (v ∘ permutationRead read) i =
      fun b => v (read (0,b)) := by
    funext b
    simp [source,permutationRead]
  have targetEq (i : Row h) : target (v ∘ permutationRead read) i =
      fun b => v (read (0,b)) := by
    funext b
    simp [target,permutationRead]
  have tagEq (i : Row h) : tag (v ∘ permutationRead read) i =
      (Computability.VPVNP.RAMSerialization.wordBits h).symm (fun b => v (read (i,b))) := by
    simp [tag,permutationRead]
  simp [coeff,Valid,sourceEq,targetEq,funext tagEq]

theorem permutation_cut {F : Type*} {V : Type} [Field F] [Fintype V] {h : ℕ}
    (read : Row h × Fin h → V) (v : V → Bool) :
    (∑ z, TypedWiring.value (readback F (permutationRead read)) (Sum.elim v z)*coeff F h h z) =
      if Function.Bijective (fun i : Row h =>
        (Computability.VPVNP.RAMSerialization.wordBits h).symm (fun b => v (read (i,b)))) then 1 else 0 :=
  (readback_contract (permutationRead read) v (coeff F h h)).trans (permutation_factor read v)

end Hierarchy.Tagged.WideHost

end
end OAI
