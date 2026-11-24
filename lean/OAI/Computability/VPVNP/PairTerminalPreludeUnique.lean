import OAI.Computability.VPVNP.PairSimulationTerminalBlocks
import OAI.Computability.VPVNP.PairSimulationTerminalTraceEquiv
import OAI.Computability.VPVNP.PairSimulationTerminalDeterministic

/-!
# Uniqueness of independently verified terminal setup records

The three mandatory setup stages force every supplied choice to be empty.
Consequently their complete chronological records, including all physical
memories, agree across independent proofs of the prelude. A shared-bit
record at that boundary is then determined by its native call list.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink
open BurstRAM LiveProgram

variable {w cap : ℕ} {workers : Stage → PairTable} {pub : Fin 11 → Word w} {m : Memory w}

theorem CompletedPhase.eq_of_choices {e : Entry w} (x y : CompletedPhase workers pub cap e m)
    (equal : x.val.choices = y.val.choices) : x = y :=
  Subtype.ext ((x.prop.block_eq_suffix y.prop (a := []) (b := []) (by rw [equal])).1)

theorem QuietPrefix.unique (p q : QuietPrefix workers pub cap m) : p=q := by
  obtain ⟨b,u,v,qb,qu,qv⟩ := p
  obtain ⟨b',u',v',_,_,_⟩ := q
  obtain rfl : b=b' := CompletedPhase.eq_of_choices b b' (b.prop.force_quiet qb b'.prop).1.symm
  obtain rfl : u=u' := CompletedPhase.eq_of_choices u u' (u.prop.force_quiet qu u'.prop).1.symm
  obtain rfl : v=v' := CompletedPhase.eq_of_choices v v' (v.prop.force_quiet qv v'.prop).1.symm
  rfl

theorem QuietPrefix.bitPaths_eq {I : Type*} (q : QuietPrefix workers pub cap m) (x y : I ≃ q.BitPaths)
    (equal : ∀ f, (x f).val.choices = (y f).val.choices) : x=y :=
  Equiv.ext fun f => CompletedPhase.eq_of_choices _ _ (equal f)

end PairSimulation.TerminalLink

end VPVNP
end Computability
end OAI
