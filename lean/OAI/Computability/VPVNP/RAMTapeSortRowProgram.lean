import OAI.Computability.VPVNP.RAMTapeSortRowModel
import OAI.Computability.VPVNP.RAMTapeSortRecordCode

/-!
# The fixed finite stack control for one sorting row

The public address routine delivers the local-stride and orientation bits.
A local row fetches both operands from the current array. A cross-site row
verifies the sent copy and then combines a freshly fetched local record
with the receive. The two physical incident streams are consumed only by
the corresponding cross-site operations.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortRow

/-- Run the row comparator on the chosen right operand and retain the minimum or maximum as
directed. -/
def select (src : RightSource) (keepMin : Bool) : FiniteRoutine Port :=
  (Sorter.select keepMin).onPorts (comparePorts src)

/-- Compare the staged local record with the outgoing record and emit the verification flag. -/
def verify : FiniteRoutine Port := Sorter.verify.onPorts (comparePorts .outgoing)

/-- Pop the public comparator orientation and consume the two staged
records. A missing address decision rejects. -/
def oriented (src : RightSource) : FiniteRoutine Port :=
  .ofRoutine (Routine.popCase Port.orientation (Routine.halt false) (select src false).body
    (select src true).body)

/-- Fetch the current row and its local partner, then apply the comparison in the requested
orientation. -/
def localPass : FiniteRoutine Port :=
  (fetch .first).followedBy ((fetch .other).followedBy (oriented .localRegister))

/-- Verify the outgoing copy against the current row, fetch that row again, and compare it with
the incoming partner. -/
def crossPass : FiniteRoutine Port :=
  (fetch .first).followedBy (verify.followedBy ((fetch .first).followedBy (oriented .incoming)))

private def branch : FiniteRoutine Port :=
  .ofRoutine (Routine.popCase Port.localFlag (Routine.halt false) crossPass.body localPass.body)

/-- Dispatch on the local-stride flag, execute the corresponding row pass, and clear the
partner offset. -/
def program : FiniteRoutine Port := branch.followedBy clearPartner

end RAMTape.SortRow

end VPVNP
end Computability
end OAI
