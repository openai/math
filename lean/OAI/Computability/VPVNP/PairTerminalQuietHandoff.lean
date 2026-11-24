import OAI.Computability.VPVNP.PairSimulationTerminalBlocks

/-! # Controller validity after a completed physical terminal phase -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink

open BurstRAM LiveProgram

variable {w cap : ℕ} {workers : Stage → PairTable} {pub : Fin 11 → Word w}

open private follow_halt from OAI.Computability.VPVNP.PairSimulationTerminalSplit

/-- A completed phase writes the actual next-stage tag and its zero cursor
before the following phase. The original worker can start from arbitrary
values at both controller addresses. -/
theorem Phase.handoffValid {e : Entry w} {m final : Memory w} {bs : List (List Bool)}
    {ls : List (Log w)}
    (phase : Phase workers pub cap e m bs ls final) (wide : 32 ≤ 2 ^ w) :
    ∀ next : Entry w, handoff e.stage = some next → next.Valid (header pub) final := by
  induction phase with
  | @last e m bs raw call room accepted =>
    intro next follows
    exact next_valid (header pub) e next raw m wide ((follow_halt e raw accepted).trans follows)
  | @more e m b bs raw x ls final call room returned tail ih =>
    intro next follows
    exact ih next follows

/-- Every completed deterministic prefix provides the actual entry to the
shared-bit stage, regardless of which vertex paths subsequently succeed. -/
theorem QuietPrefix.valid_sharedBits {m : Memory w} (q : QuietPrefix workers pub cap m)
    (wide : 32 ≤ 2 ^ w) :
    (Entry.resume Stage.sharedBits (0 : Word w)).Valid (header pub) q.traversalRows.val.memory :=
  q.traversalRows.prop.handoffValid wide _ rfl

end PairSimulation.TerminalLink

end VPVNP
end Computability
end OAI
