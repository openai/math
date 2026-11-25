import OAI.Computability.BorderVNP.ShortenEpochDirections

/-!
# Finite enumeration for product deck samples

The finite-sample theorems for an abstract factor index use classical
decidable equality to enumerate products and permutations. The scope below
selects the same enumeration when specializing those theorems to the actual
Boolean cube. The size of the cube depends on the variable dimension.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch.Cube

/-- Use the equality test of the abstract finite-factor motion theorems when
constructing their product and permutation types over the Boolean cube. -/
@[reducible] noncomputable scoped instance (priority := 2000) classicalDecEq (D : ℕ) : DecidableEq (Cube D) :=
  fun a b => Classical.propDecidable (a = b)

end Epoch.Cube

end BorderVNP
end Computability
end OAI
