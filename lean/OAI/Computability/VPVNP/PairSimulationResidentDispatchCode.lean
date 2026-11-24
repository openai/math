import OAI.Computability.VPVNP.PairSimulationResidentMapDispatch
import OAI.Computability.VPVNP.PairSimulationMapDriverCode

/-!
# Fixed code for the demand and party dispatch

A table's two instructions per entry are assembled once and then relocated
into the enclosing shrinking or refreshing role. All control words fit the
small literal format used by the live vertex program.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ResidentMapDispatch.Cases

open BurstRAM BurstRAM.PrivateRAM
open MapDriver.Program (remaining)

variable {X : Type*} {w p r k : ℕ} (C : Cases X p r)

/-- The address of a case's zero test (`false`) or decrement (`true`). -/
def address : X × Bool → Fin p
  | (x, false) => C.test x
  | (x, true) => C.subtract x

/-- The zero test jumps to the case target on a match. The decrement continues with the tail. -/
noncomputable def text : X × Bool → Instr 5 p r k
  | (x, false) => .jumpEq C.index C.zero (C.target x) (C.subtract x)
  | (x, true) => .binary .sub C.index C.index C.one (C.start (remaining x C.items))

private theorem linked_from (M : Machine w p r k)
    (h : ∀ a, M.code (C.address a) = (C.text a).resize w)
    (xs : List X) (nodup : xs.Nodup)
    (suffix : ∀ x ∈ xs, remaining x C.items = remaining x xs) : C.Linked M xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨fresh, nd⟩ := List.nodup_cons.mp nodup
    have tail : remaining x C.items = xs := (suffix x (List.mem_cons_self ..)).trans
      (by simp [remaining])
    refine ⟨h (x, false), ?_, ih nd ?_⟩
    · change M.code (C.address (x, true)) = _
      rw [h]
      change Instr.binary .sub C.index C.index C.one (C.start (remaining x C.items)) = _
      rw [tail]
    · intro y hy
      have ne : y ≠ x := fun eq ↦ fresh (eq ▸ hy)
      exact (suffix y (List.mem_cons_of_mem _ hy)).trans (by simp [remaining, ne])

/-- Installing the emitted instructions supplies the case-chain link
for every fixed enumerated list, including the empty list. -/
theorem linked (M : Machine w p r k) (nodup : C.items.Nodup)
    (rows : ∀ a, M.code (C.address a) = (C.text a).resize w) : C.Linked M C.items :=
  linked_from C M rows C.items nodup fun _ _ ↦ rfl

end PairSimulation.ResidentMapDispatch.Cases

end VPVNP
end Computability
end OAI
