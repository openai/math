import OAI.Computability.BorderVNP.TransmissionSiteRowContext
import OAI.Computability.BorderVNP.TeamSiteTraversalSort

/-! # Identifying the installed endpoint and memory checks with team traversal

The public first frame or the shared predecessor bits determine the typed input.
The final owner tests for a halt, and every other owner compares every successor
bit. The rows used by the physical sorter begin at the same addresses and clock
offsets as the traversal's chronological rows.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RAMTape TeamTapeHandoff TeamSite TeamSite.Processor
open TeamSiteTraversal (Reads Writes)

variable {pc reg k routines m g R r w a n e : ℕ} {Q Γ : Type}
variable {P : TeamOpcode.Program pc reg k routines} {lib : Fin routines → Macro Q Γ m g}
variable {S : SiteData R r reg k w a} {u : Fin (R+1)} {j : Fin r}
    {int : Wires.Edge r reg w e (w+1) → Bool} {f : Frame w reg}
    {raw data : List Bool} {address : ℕ} {X : Row.Context P lib n (Nat.clog 2 r) e w}

/-- The traversal predicate reads exactly the sender or public frame chosen by the
real local processor. At the first site this uses injectivity of the frame bits. -/
theorem ingress_eq_iff (start f : Frame w reg) (int : Wires.Edge r reg w e (w+1) → Bool) (j : Fin r) :
    f.bits = ingress start int j ↔ Reads (Wires.edgeEquiv int).1 start j f := by
  by_cases first : j.val = 0
  · simp only [ingress,Reads,first,ite_true]
    exact Frame.bits_injective.eq_iff
  · simp only [ingress,Reads,first,ite_false]

/-- The actual guard for a proposed endpoint is the traversal's full frame comparison
at an interior owner and its accepting-halt test at the last owner. -/
theorem RowInstalled.guard_iff (h : RowInstalled S u j int f raw data address X) (out : Frame w reg) :
    X.guard out = true ↔ Writes (Wires.edgeEquiv int).1 j out := by
  have bound := j.isLt
  by_cases interior : j.val+1 < r
  · have later : j.val+1 ≠ r := by omega
    simp [Row.Context.guard,h.lastEq,last,later,h.outgoing,egress,Writes,interior]
  · have final : j.val+1 = r := by omega
    simp [Row.Context.guard,h.lastEq,last,final,Writes]

/-- The two real sorting lanes read the chronological probes for exactly this owner,
starting at its global input address and at the tick of the decoded predecessor. -/
theorem RowInstalled.sorted_iff (h : RowInstalled S u j int f raw data address X)
    (rows : Fin r → List Bool) (source : data = rows j)
    (offset : address = TeamTapeInputEmit.rowStart rows j) (es : List (TeamRAM.Event w)) :
    X.sorted es ↔ TeamSiteTraversal.sorted X.hw₂ X.capacity rows int j f es := by
  have eq : X.rows es = fun v => if v = Wires.primary j then
      TeamTapeInputEmit.records (w+1) (TeamTapeInputEmit.rowStart rows j) (rows j) ++
        TeamEventRecords.historySlots (f.elapsed.val+1) es else [] := by
    funext v
    simp only [Row.Context.rows,Row.Context.slots,h.primaryEq,h.initialEq,h.frameEq,source,offset,chunkSlots]
  simp only [Row.Context.sorted,TeamSiteTraversal.sorted,eq,h.primaryEq,h.secondaryEq,h.fieldsEq]

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
