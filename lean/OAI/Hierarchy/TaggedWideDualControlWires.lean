import OAI.Hierarchy.TaggedWideDualControlRows
import OAI.Hierarchy.TaggedWideControlWires

namespace OAI
/-! # A parent tag and the two distinct native sorting transcripts -/

noncomputable section
namespace Hierarchy.Tagged.WideHost
open scoped Classical BigOperators
variable {V F : Type*} [Field F] {h m₀ m₁ : ℕ}

open DualControlIndex

private def bankWires (sort₀ : Fin 28→Fin (pins m₀ m₀)→V) (sort₁ : Fin 28→Fin (pins m₁ m₁)→V) :
    (j : Bank)→Fin (pins (bankSize m₀ m₁ j) (bankSize m₀ m₁ j))→V
  | .inl i=>sort₀ i
  | .inr i=>sort₁ i

def dualControlWires (tagPort : Row h×Fin h→V) (sort₀ : Fin 28→Fin (pins m₀ m₀)→V)
    (sort₁ : Fin 28→Fin (pins m₁ m₁)→V) :
    (j : Fin 57)→Fin (pins (dualControlSizes h m₀ m₁ j) (dualControlSizes h m₀ m₁ j))→V :=
  Fin.cases (permutationRead tagPort) (fun i=>bankWires sort₀ sort₁ (side i))

/-- The read on occurrence zero is tag authenticity. Every other read
belongs to the prefix or the paid sorting network at its true width. -/
theorem dual_control_product (tagPort : Row h×Fin h→V) (sort₀ : Fin 28→Fin (pins m₀ m₀)→V)
    (sort₁ : Fin 28→Fin (pins m₁ m₁)→V) (x : V→Bool) :
    (∏j,coeff F (dualControlSizes h m₀ m₁ j) (dualControlSizes h m₀ m₁ j)
      (x ∘ dualControlWires tagPort sort₀ sort₁ j)) =
      (if Function.Bijective (fun i : Row h=>(Computability.VPVNP.RAMSerialization.wordBits h).symm
        (fun b=>x (tagPort (i,b)))) then 1 else 0) *
        (∏i,coeff F m₀ m₀ (x ∘ sort₀ i)) * ∏i,coeff F m₁ m₁ (x ∘ sort₁ i) := by
  let f : Bank→F := fun j=>coeff F (bankSize m₀ m₁ j) (bankSize m₀ m₁ j) (x ∘ bankWires sort₀ sort₁ j)
  rw [Fin.prod_univ_succ]
  change coeff F h h (x ∘ permutationRead tagPort)*(∏ j : Fin 56,f (side j))=_
  rw [permutation_factor,side.prod_comp f,Fintype.prod_sum_type,mul_assoc]; rfl

end Hierarchy.Tagged.WideHost

end
end OAI
