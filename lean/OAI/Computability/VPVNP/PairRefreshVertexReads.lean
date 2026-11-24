import OAI.Computability.VPVNP.PairRefreshVertexPrefix
import OAI.Computability.VPVNP.PairShrinkRoleChildReads
import OAI.Computability.VPVNP.PairVertexLevelReads

/-!
# External read footprint of the refresh locator and singleton child reader

The locator reads the header and level scalars. The child reads its descriptor,
the old directory, and the incoming and width arrays. The two handoff copies
and the ordinal-bank initializer use only private registers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshVertexAssembly

open BurstRAM Compression CompressorRecords NodeArguments NodeArguments.ChildScan
open TraversalControllerInputs TraversalRoles ShrinkRole.ChildArguments
open scoped Fin.CommRing

variable {w a g : ℕ} {pub : Fin 11 → Word w} {m : Memory w}
  {head first pitch offset cap base : ℕ} {initial : TaggedLayer} {ls : List (Fiber w)}

theorem inputTrace_reads (heads : Resident pub m head first pitch offset cap base initial ls)
    (beforeH : ∀ i ≤ ls.length, first+i*pitch+28 ≤ head)
    (X : State a g) (site : X.network.Site) (old : X.network.Half site) (U : IncidenceDirectory w)
    (listHead : ℕ) (node : Word w) (level later : ℕ) (live : level+1+later ≤ ls.length)
    (rep : U.ActualColumns X m) (col : ColumnsBelow U X head)
    (parent : node.val+1 < head) (row : listHead+1 ≤ head) :
    SourceTransport.Reads (TerminalLink.workerCell (TerminalLink.header pub))
      (inputTrace a X site old U m listHead pub node level later) := by
  let H := TerminalLink.header pub
  have hval : H.val = head := (congrArg Fin.val heads.header).trans (Nat.mod_eq_of_lt (by have := heads.headerFits; omega))
  have room : H.val + 32 ≤ 2^w := hval ▸ heads.headerFits
  have lfit := heads.levelFits level (by omega)
  have oldBase : (levelHead pub m level+14).val = first+level*pitch+14 := by
    rw [levelHead, terminal_read heads 16 (by decide), terminal_read heads 17 (by decide),
      heads.firstHead,heads.levelPitch,show (14 : Word w) = ((14 : ℕ) : Word w) from rfl,
      ← Nat.cast_mul,← Nat.cast_add,← Nat.cast_add,Fin.val_natCast,Nat.mod_eq_of_lt (by omega)]
  have headerBound : (levelHead pub m level+14).val + 6 < head := by
    rw [oldBase]; have := beforeH level (by omega); omega
  have childReads := trace_reads_below rep col node (levelHead pub m level+14) listHead
    [Child.ofHalf X site old] parent headerBound row
  have childWorker := worker_reads_of_below H room (hval ▸ childReads)
  have locate := VertexLevel.trace_worker_reads heads beforeH (level+1) later live
  intro q v hq
  rcases List.mem_append.mp hq with h | h
  · exact locate q v h
  · rcases List.mem_append.mp h with h | h
    · simp at h
    · rcases List.mem_append.mp h with h | h
      · simp [List.mem_replicate] at h
      · exact childWorker q v h

end PairSimulation.RefreshVertexAssembly

end VPVNP
end Computability
end OAI
