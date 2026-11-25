import OAI.Hierarchy.DescentSeedSiteGeometry

namespace OAI
namespace Hierarchy.DescentSeedRoot
noncomputable section
def index {T : Type} [Fintype T] (t : T) := ((Fintype.equivFin T) t).val

end
end Hierarchy.DescentSeedRoot

namespace Hierarchy.DescentPackedSeed
open DescentSeedRoot Catalyst
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {k n : ℕ} (X : Approximation F k n)
def leg (v : Vertex X) : Fin (legArity X v)→LocalBoundary X v :=
  match v with
  | .inl u=>(Fintype.equivFin (LocalBoundary X (.inl u))).symm
  | .inr i=>Fin.cons (.inl ⟨.inr i,Or.inr rfl⟩) (fun _=>.inr ⟨i,rfl⟩)


end
end Hierarchy.DescentPackedSeed

end OAI
