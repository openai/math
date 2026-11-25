import OAI.Hierarchy.DescentInitialHost
import OAI.Hierarchy.DescentSeedOriginalVertex

namespace OAI
/-! The original finite sites, immutable incidence arity and inverse padded host names. -/
namespace Hierarchy
open DescentInitialHost Catalyst
open scoped Classical
noncomputable section

variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p)
local notation "N" => X.network.copyGraph

namespace DescentSeedRoot
abbrev Vertex := Site N
abbrev Cable := Wire N
end DescentSeedRoot

namespace DescentPackedSeed
open DescentSeedRoot
abbrev LocalBoundary (v : Vertex X) :=
  {e : Cable X // source X.network.copyGraph e=v ∨ target X.network.copyGraph e=v} ⊕
    {p : Fin (Fintype.card (Port p X.width)) // Sum.inr p=v}

def legArity : Vertex X→ℕ
  | .inl u=>Fintype.card (LocalBoundary X (.inl u))
  | .inr _=>2

end DescentPackedSeed

namespace DescentSeedInitialTable
def rack {H : ℕ} (host : Site X.network.copyGraph ↪ Fin H) (h : Fin H) :
    Option (Site X.network.copyGraph) := by
  classical
  exact if present : ∃u,host u=h then some present.choose else none

omit [Field F] in
theorem rack_real {H : ℕ} (host : Site X.network.copyGraph ↪ Fin H) (v : Site X.network.copyGraph) :
    rack X host (host v)=some v := by
  classical
  have present : ∃u,host u=host v := ⟨v,rfl⟩
  rw [rack,dite_eq_left present]
  exact congrArg some (host.injective present.choose_spec)

end DescentSeedInitialTable
end
end Hierarchy

end OAI
