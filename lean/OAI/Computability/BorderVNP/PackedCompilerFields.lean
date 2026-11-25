import OAI.Computability.BorderVNP.PackedCompilerRows
import OAI.Computability.BorderVNP.PackedFieldBoundGrid

/-! # Shape and scalar bounds of an installed one-copy site table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing

/-- Both the fixed template shapes and the two numeric scales of the actual
one-copy tables are present in the final compiler input. -/
def Site.CompilerFields {D m : ℕ} {K : Type*} [Field K] (s : Site) (e : PaidIdentity K D m) (V U : ℕ) : Prop :=
  s.CompilerRows e ∧ s.SplitFields V U

end Packing.Inherited

end BorderVNP
end Computability
end OAI
