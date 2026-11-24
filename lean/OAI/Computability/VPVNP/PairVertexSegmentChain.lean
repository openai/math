import OAI.Computability.VPVNP.PairVertexImage

/-!
# Sequencing native vertex segments

The two code ranges are consecutive. The first segment's successful continuation
is the entry of the second. Register placements are explicit so a preparation block
can fill the operands of its successor and disjoint scratch banks can be framed.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage.Segment

open BurstRAM BurstRAM.PrivateRAM

variable {p r n w : ℕ}

/-- Program counters for the first segment in a consecutive two-segment instruction range. -/
def leftPC (A B : Segment) (loc : Fin (A.count + B.count) → Fin p) (j : Fin A.count) :=
  loc (j.castAdd B.count)

/-- Program counters for the second segment, shifted past all instructions of the first. -/
def rightPC (A B : Segment) (loc : Fin (A.count + B.count) → Fin p) (j : Fin B.count) :=
  loc (j.natAdd A.count)

/-- The two segments may use the same register for an explicit operand handoff. -/
def thenWith (A B : Segment) (lhs : Fin A.privateRegs ↪ Fin n)
    (rhs : Fin B.privateRegs ↪ Fin n) : Segment where
  count := A.count + B.count
  privateRegs := n
  entry := A.entry.castAdd B.count
  row loc dfs saved reg done := Fin.addCases
    (A.row (leftPC A B loc) dfs saved (lhs.trans reg) (rightPC A B loc B.entry))
    (B.row (rightPC A B loc) dfs saved (rhs.trans reg) done)

/-- Separate the two private register files while keeping the shared DFS and saved registers. -/
def seq (A B : Segment) := thenWith A B (Fin.castAddEmb B.privateRegs) (Fin.natAddEmb A.privateRegs)

variable (A B : Segment) (lhs : Fin A.privateRegs ↪ Fin n) (rhs : Fin B.privateRegs ↪ Fin n)
    (loc : Fin (A.count + B.count) → Fin p) (dfs : Fin 9 ↪ Fin r) (saved : Saved ↪ Fin r)
    (reg : Fin n ↪ Fin r) (done : Fin p) (M : Machine w p r 11)

theorem split_link (rows : ∀ j, M.code (loc j) =
    ((thenWith A B lhs rhs).row loc dfs saved reg done j).resize w) :
    (∀ j, M.code (leftPC A B loc j) =
      (A.row (leftPC A B loc) dfs saved (lhs.trans reg) (rightPC A B loc B.entry) j).resize w) ∧
    (∀ j, M.code (rightPC A B loc j) =
      (B.row (rightPC A B loc) dfs saved (rhs.trans reg) done j).resize w) := by
  constructor
  · intro j
    simpa only [thenWith, Fin.addCases_left, leftPC] using rows (j.castAdd B.count)
  · intro j
    simpa only [thenWith, Fin.addCases_right, rightPC] using rows (j.natAdd A.count)

end PairSimulation.VertexImage.Segment

end VPVNP
end Computability
end OAI
