import OAI.Computability.VPVNP.PairVertexStagePrefix
import OAI.Computability.VPVNP.PairVertexStageSegment

/-!
# Shared locator registers across stage-specific bodies

Register banks chosen by a matrix table need not have the same numerical ordering as the
child and hidden routines. Number the complement of the fourteen locator words separately.
Every stage then uses the shared prefix required by the finite stage dispatcher.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation

open VertexImage

/-- A vertex segment together with an embedding of the fourteen registers needed to locate its
active level. -/
structure LocatedBody where
  /-- The executable segment of a body that shares a level locator. -/
  code : Segment
  /-- Identify the body's fourteen level-locator registers within its private register space. -/
  locator : Fin 14 ↪ Fin code.privateRegs

namespace LocatedBody

variable (B : LocatedBody)

/-- The body's private registers outside the image of its shared locator embedding. -/
abbrev Tail := {i : Fin B.code.privateRegs // i ∉ Set.range B.locator}
/-- Number of additional private registers required beyond the shared locator bank. -/
noncomputable abbrev tailCount := Nat.card B.Tail

/-- Number the other registers separately and retain the order of the locator. -/
noncomputable def order : Fin (14 + B.tailCount) ≃ Fin B.code.privateRegs := by
  classical
  let other : B.Tail ≃ Fin B.tailCount := Fintype.equivFinOfCardEq Nat.card_eq_fintype_card.symm
  exact finSumFinEquiv.symm.trans
    (((Equiv.ofInjective B.locator B.locator.injective).sumCongr other.symm).trans
      (Equiv.Set.sumCompl (Set.range B.locator)))

theorem order_locator (i : Fin 14) : B.order (i.castAdd B.tailCount) = B.locator i := by
  classical
  simp [order]
  rfl

/-- Only the numerical operand placement changes. The PC and native opcode are identical. -/
noncomputable def normalized : Segment where
  count := B.code.count
  privateRegs := 14 + B.tailCount
  entry := B.code.entry
  row loc dfs saved reg done := B.code.row loc dfs saved (B.order.symm.toEmbedding.trans reg) done

/-- Append fresh child registers after every register of the remaining routine. -/
def withChildren (a : ℕ) : LocatedBody where
  code := VertexStagePrefix.withChildren a B.code B.locator
  locator := B.locator.trans
    (Fin.castAddEmb (NodeArguments.ChildCode.RegisterBank.segment a).privateRegs)

variable {N : ℕ}

/-- One finite image starts with the real level scan and selects the stage within the block. -/
noncomputable def family (bodies : Fin N → LocatedBody) : Segment :=
  VertexStageDispatch.locatedFamily (fun i => (bodies i).normalized) (fun i => (bodies i).tailCount)
    (fun _ => rfl)

end LocatedBody

end PairSimulation

end VPVNP
end Computability
end OAI
