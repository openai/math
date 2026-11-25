import OAI.Computability.BorderVNP.DiagonalJointSparseWindow
import OAI.Computability.BorderVNP.DiagonalUniformPostReceipt
import OAI.Computability.BorderVNP.DiagonalSupportedVisitFinish

/-! # The all-team clock from a physical receipt on each returning owned finish -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open VPVNP.BurstRAM CompactMachine CellMacro.Generator BorderVNP.Cube BorderVNP.Cube.Tally ScheduleClock
open TeamContraction TeamContraction.JointHeader TeamContraction.JointHeader.PositiveFields TeamContraction.ProcessorSlots
open DiagonalTallyCellReports SignedTaskArena

variable {R n w dim box lanes selectors symbols : ℕ}
    (id : TableEntry dim box lanes selectors symbols → ℕ) (U : Fin (R+1) → PinStart SparseExterior.driver n w)
local notation3 (prettyPrint := false) "mac(" u ")" => install SparseExterior.driver n (U u).routines
local notation3 (prettyPrint := false) "pin(" a "," u ")" => (U u).pins (a u).1

variable (used : Fin (R+1) → ℕ) (l : Fin (R+1) → SignedTaskArena.Layout) (A : Fin (R+1) → StartupArena)
    (batch X P L fixed K F H d subt read : ℕ)
local notation3 (prettyPrint := false) "cost" => uniformWindows batch (R+1) X P L K fixed F H

/-- Combine each real local finish, including those obtained from inconsistent
shared subtotals, into the uniform window. On the lead team the claimed bits
are passed to the staged reader. On all other teams the original team number
is retained and the reader's ordinary guard returns immediately. -/
theorem JointClock.ofPhysicalPost
    (before : ∀ (a : JointPrefix id U) u, let v := visits id U (a u)
      used u+traceCost pin(a,u).val.1+traceCost v.profile.val.1+traceCost v.routing.val.1 ≤ (cost).core+(cost).before)
    (arguments : ∀ (a : JointPrefix id U) u, let input := afterRoute id U (a u)
      traceCost input.val.1+privateDirectoryTicks (U u).pub input.val.2.2 ≤ (cost).argumentsCalls)
    (post : ∀ (a : JointPrefix id U) u, let p := (a u).2
      ∀ q : Returns callOwnedCells (U u).pub mac(u) p.val.2.1 p.val.2.2,
      ∀ z : Returns (finishExpansion signedOccurrences) (U u).pub mac(u) q.val.2.1 q.val.2.2,
        Nonempty (PhysicalPost (d:=d) (width:=subt) u (l u) P L F H (U u).pub mac(u) q.val.2.1 q.val.2.2 z))
    (frame : ∀ u, ((U u).pub 0).val=(A u).frame)
    (placement : ∀ u,(A u).next ≤ (l u).cube.header.header)
    (number : ∀ (a : JointPrefix id U) u, let p := (a u).2
      ∀ q : Returns callOwnedCells (U u).pub mac(u) p.val.2.1 p.val.2.2, (q.val.2.2 ((U u).pub 0).val).val=u.val)
    (rectangle : 512*((R+1)+1)*(d+1)*(w+1)+(7+read) ≤ batch)
    (lead : ∀ (a : JointPrefix id U), let p := (a (0 : Fin (R+1))).2
      ∀ q : Returns callOwnedCells (U 0).pub mac(0) p.val.2.1 p.val.2.2,
      ∀ z : Returns (finishExpansion signedOccurrences) (U 0).pub mac(0) q.val.2.1 q.val.2.2,
      PhysicalPost (d:=d) (width:=subt) (0 : Fin (R+1)) (l 0) P L F H (U 0).pub mac(0) q.val.2.1 q.val.2.2 z →
      ∀ v : Returns leadEntry (U 0).pub mac(0) z.val.2.1 z.val.2.2, traceCost v.val.1 ≤ 7+read) :
    JointClock id U used cost := by
  refine ⟨before,arguments,?_,?_⟩
  · intro a u p q z
    obtain ⟨b⟩ := post a u q z
    exact uniform_finish_of_packet b.measured b.occupied b.slots b.localUnits (by omega)
  · intro a u p q z v
    obtain ⟨b⟩ := post a u q z
    change traceCost v.val.1 ≤ batch
    by_cases same : u=0
    · subst u
      exact (lead a q z b v).trans (by omega)
    · have off : u.val≠0 := fun h => same (Fin.ext (by simpa only [Fin.val_zero] using h))
      exact (b.receipt.nonleadTicks (l u) (A u) b.location b.retained (frame u) (placement u) (number a u q)
        off z v).trans (by omega)

end RoutingISA.Evaluator.PinStart

end BorderVNP
end Computability
end OAI
