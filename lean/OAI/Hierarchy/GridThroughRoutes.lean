import OAI.Hierarchy.GridThrough
import OAI.Hierarchy.GridLensWireRoutes

namespace OAI
/-! # Physical rail labels of the equalities in a programmed grid -/

namespace Hierarchy.GridThrough.Program
open scoped Classical
open GridLens
noncomputable section

variable {E k n p : ℕ} {width : Fin k → ℕ} (P : GridThrough.Program (Fin E) n p width)

/-- Physical geometric label read from a native equality edge or reserved cell passage. -/
def physicalRoute : (P.Edge ⊕ (Cell k n × Catalyst.Wire width)) → WireRoute k n E
  | .inl (.inl (e,false)) => .segment e (.inl (.inl ())) false
  | .inl (.inl (e,true)) => .segment e (.inl (.inr (.inr ()))) false
  | .inl (.inr (.inl (e,t))) => .segment e (.inl (.inr (.inl t))) false
  | .inl (.inr (.inr (.inl z))) => .through z.val.1 z.val.2 false
  | .inl (.inr (.inr (.inr u))) => .segment u.1.val.1 (.inr (u.1.val.2,u.2)) u.2
  | .inr (c,w) => .through (P.pass c w) (c (P.direction (P.pass c w))) false

/-- Recover the true constructor from an occurrence in the actual equality-test list. -/
def edgeDecode : Fin P.wiring.equal.length ≃ P.Edge :=
  (finCongr (by simp [wiring])).trans P.edgeOrdinal.symm

@[simp] theorem equal_get (i : Fin P.wiring.equal.length) :
    P.wiring.equal.get i = P.edgePair (P.edgeDecode i) := by
  exact List.get_ofFn _ _

/-- This inverse table identifies each demand at its actual equality or mounted cell ordinal. -/
def demandDecode : Demand P.wiring.equal.length ((n+1)^k) width ≃
    P.Edge ⊕ (Cell k n × Catalyst.Wire width) :=
  Equiv.sumCongr P.edgeDecode (Equiv.prodCongr cellOrdinal.symm (Equiv.refl _))

end
end Hierarchy.GridThrough.Program

end OAI
