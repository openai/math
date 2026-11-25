import OAI.Computability.BorderVNP.DiagonalPhysicalPinStart

/-! # The public domain of jointly returning native preparations -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open VPVNP.BurstRAM CompactMachine CellMacro.Generator BorderVNP.Cube
open scoped BigOperators Classical

variable {R n w axes b h K s : ℕ} {id : TableEntry axes b h K s → ℕ} {gen : Fragment IO}
    {X : Type} {positive : X → Prop} (U : {x // positive x} → Fin (R+1) → PinStart gen n w)

/-- A shared exterior has pre-call support if it agrees at startup and every
team can finish its preparation on the physical banks supplied by that startup. -/
def preCallSupport (id : TableEntry axes b h K s → ℕ) (x : X) : Prop :=
  ∃ hx : positive x, jointSupport id (U ⟨x,hx⟩)

/-- Extract the local returning prefixes on the supported part of the
ordinary exterior type used to index the evaluated column. -/
theorem preCallSupport_iff (x : X) (hx : positive x) :
    preCallSupport U id x ↔ jointSupport id (U ⟨x,hx⟩) :=
  ⟨fun ⟨_,r⟩ => r,fun r => ⟨hx,r⟩⟩

/-- On a shared exterior that passes startup and lacks joint support, the
native product vanishes as soon as each missing prefix excludes an accepting
run on its team. This criterion includes all prefixes with zero reader value. -/
theorem product_zero_off_support (x : X) (hx : positive x) (bad : ¬ preCallSupport U id x)
    (value : Fin (R+1) → ℤ)
    (missing : ∀ u, ¬ Nonempty ((U ⟨x,hx⟩ u).Prefix id) → value u = 0) : ∏ u, value u = 0 := by
  classical
  have empty : ¬ ∀ u, Nonempty ((U ⟨x,hx⟩ u).Prefix id) :=
    fun all => bad ((preCallSupport_iff U x hx).2 all)
  obtain ⟨u,none⟩ := not_forall.mp empty
  exact Finset.prod_eq_zero (Finset.mem_univ u) (missing u none)

end RoutingISA.Evaluator.PinStart

end BorderVNP
end Computability
end OAI
