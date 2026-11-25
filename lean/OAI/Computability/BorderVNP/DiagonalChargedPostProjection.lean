import OAI.Computability.BorderVNP.DiagonalIssuedJointCharge

/-! # The argument and post-call part of a charged native visit -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open VPVNP.BurstRAM CompactMachine CellMacro.Generator TeamContraction.ProcessorSlots
open RoutingISA.SignedTaskArena ScheduleClock

/-- The argument, input reader, and post executions of one original prefix,
with the same continuation register bank in each returned call. -/
def ChargedPost {R n w a b h K s : ℕ} (id : Cube.TableEntry a b h K s → ℕ)
    (U : Fin (R+1) → PinStart SparseExterior.driver n w) (budget : ℕ)
    (task : SignedTaskArena.Layout) (A : StartupArena)
    (entryWords indexBits dim subt P L F H : ℕ) (run : JointPrefix id U) (u : Fin (R+1)) : Prop :=
  let p := run u
  let input := afterRoute id U p
  let mac := install SparseExterior.driver n (U u).routines
  traceCost input.val.1+privateDirectoryTicks (U u).pub input.val.2.2≤budget ∧
  ReaderKept A entryWords indexBits (U u).memory ((U u).pins p.1).val.2.2 p.2.val.2.2 ∧
  ∀ call : Returns callOwnedCells (U u).pub mac p.2.val.2.1 p.2.val.2.2,
    ∀ z : Returns (finishExpansion signedOccurrences) (U u).pub mac call.val.2.1 call.val.2.2,
      Nonempty (PhysicalPost (teams:=R+1) (d:=dim) (width:=subt) u task P L F H
        (U u).pub mac call.val.2.1 call.val.2.2 z)


/-- Join the genuine front cost to the argument and post on this same return. -/
theorem ChargedPost.withFront {R n w a b h K s : ℕ} {id : Cube.TableEntry a b h K s → ℕ}
    {U : Fin (R+1) → PinStart SparseExterior.driver n w} {used : Fin (R+1) → ℕ}
    {cost : PhaseCharges} {task : SignedTaskArena.Layout} {A : StartupArena}
    {entryWords indexBits dim subt P L F H : ℕ} {run : JointPrefix id U} {u : Fin (R+1)}
    (post : ChargedPost id U cost.argumentsCalls task A entryWords indexBits dim subt P L F H run u)
    (front : used u+traceCost ((U u).pins (run u).1).val.1+
      traceCost (visits id U (run u)).profile.val.1+traceCost (visits id U (run u)).routing.val.1 ≤ cost.core+cost.before) :
    ChargedVisit id U used cost task A entryWords indexBits dim subt P L F H run u :=
  ⟨front,post⟩

end RoutingISA.Evaluator.PinStart

end BorderVNP
end Computability
end OAI
