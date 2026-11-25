import OAI.Hierarchy.DescentBundleTerminal

namespace OAI
/-! # The retained word capacity at one original scalar node -/
namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory Finset
open scoped Classical BigOperators
noncomputable section
variable {Tag A:Type} {w:A→ℕ} {p:ℕ} {r:BitRecipe Tag A w}

theorem Shape.node_keys_mul (s:Shape p r) (hp:0<p) (u:r.Node) (R:ℕ)
    (stride:∀j g,(s.chunk u j g).stride≤R) :
    (s.keys u).length*p≤(R+1)*r.nodeBits u := by
  change (s.recipe hp).arity u*p≤_
  rw [s.recipe_refs]
  unfold BitRecipe.nodeBits
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply sum_le_sum
  intro j _
  rw [s.size_eq]
  calc
    _ ≤ ∑_g : Fin (s.groups u j),(R+1)*p := sum_le_sum fun g _ =>
      Nat.mul_le_mul_right _ ((s.chunk u j g).bound.trans (Nat.add_le_add_right (stride j g) 1))
    _ = _ := by simp [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]


/-- It suffices to reserve the scaled maximum mass of one birth node. No
site population multiplier enters this individual pointer-strip capacity. -/
theorem Shape.node_keys_le (s:Shape p r) (hp:0<p) (u:r.Node) (R cap:ℕ)
    (stride:∀j g,(s.chunk u j g).stride≤R) (mass:r.nodeBits u≤p*cap) :
    (s.keys u).length≤(R+1)*cap := by
  apply Nat.le_of_mul_le_mul_right _ hp
  calc
    _ ≤ (R+1)*r.nodeBits u := s.node_keys_mul hp u R stride
    _ ≤ (R+1)*(p*cap) := Nat.mul_le_mul_left _ mass
    _ = _ := by ring

end
end Hierarchy.DescentBundleHistory

end OAI
