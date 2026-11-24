import OAI.Computability.VPVNP.PairRefreshHookReader
import OAI.Computability.VPVNP.PairRefreshVertexPacket
import OAI.Computability.VPVNP.PairShrinkOldHalfAddresses

/-!
# Physical packets and the DFS stack across a refresh hook

The scratch projection of a stored parent supplies all independent native
slot operands. Loading the unique refresh child performs exactly the packet
write in the hook reader. The load and the selected map preserve the DFS
registers and every stack word below the scratch boundary.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook

open BurstRAM PrivateRAM Compression CompressorRecords.RefreshMapOperands DFS
open NodeArguments NodeArguments.ChildScan
open scoped Fin.CommRing

variable {w a g n p r : ℕ}

/-- Decode each field from the popped packet in the native private memory. -/
theorem stored_nodeFields (X : State a g) (v : X.network.Site) (new : X.network.Half v)
    (A : Arena) (node : ℕ) (priv : Word w → Word w)
    (fit : (Packet.mk node (packed X v new)).Fits A w n)
    (stored : (Packet.mk node (packed X v new)).Stored A (scratch n priv)) :
    NodeFields A node X v new priv :=
  Packet.read_field X v new A node priv fit stored

variable (X : State a g) (v : X.network.Site) (old : X.network.Half v) (A : Arena) (older cap : ℕ)
local notation "child" => childNode X older cap v
local notation "data" => Child.ofHalf X v old
local notation "loaded" => Child.packet X older cap (Child.ofHalf X v old)

/-- The unique packet assembled by the native half reader is the packet
whose logical update precedes the canonical refresh action. -/
theorem child_packet : loaded = packet X v child old := by
  change Packet.mk child ((data).payload X) = Packet.mk child (packed X v old)
  rw [Child.payload_ofHalf]

theorem child_scratch {priv next : Word w → Word w}
    (load : next = storePackets A [loaded] priv) :
    scratch n next = (packet X v child old).write A (scratch n priv) := by
  rw [load,scratch_storePackets,child_packet]
  rfl

/-- The load writes the child's argument interval, entirely above the stack.
Its ordinary registers are in a private bank disjoint from every DFS register. -/
theorem child_frame {front : ℕ} (dfs : Fin 9 ↪ Fin r) (bank : Fin front ↪ Fin r)
    (apart : ∀ i j, bank i ≠ dfs j) (c mid : Config w p r)
    (load : mid.privateMem = storePackets A [loaded] c.privateMem)
    (per : mid.persistent = c.persistent)
    (regs : ∀ i, i ∉ Set.range bank → mid.reg i = c.reg i)
    (fit : (packet X v child old).Fits A w n) : ShrinkRole.Frame dfs n c mid := by
  refine ⟨fun i _ => regs _ (fun ⟨j,hj⟩ => apart j i hj), ?_, per⟩
  intro q hq
  exact (congrFun load q).trans (RefreshVertexPacket.outside X v old A older cap c.privateMem
    fit.2.2 q (.inl (hq.trans_le fit.1)))

/-- The map can change the histogram and its work area. Every stack address
is below both, and each histogram address has its genuine natural value. -/
theorem body_frame {h bankSize histBase dir : ℕ} (dfs : Fin 9 ↪ Fin r) (bank : Fin bankSize ↪ Fin r)
    (apart : ∀ i j, bank i ≠ dfs j) (mid out : Config w p r)
    (per : out.persistent = mid.persistent)
    (regs : ∀ j, (∀ i, j ≠ bank i) → out.reg j = mid.reg j)
    (mem : ∀ q : Word w, q.val < dir →
      (∀ i : Fin h, q ≠ ((histBase+i.val : ℕ) : Word w)) → out.privateMem q = mid.privateMem q)
    (low : n ≤ histBase) (work : n ≤ dir) (histFit : histBase+h ≤ 2^w) :
    ShrinkRole.Frame dfs n mid out := by
  refine ⟨fun i _ => regs _ (fun j eqn => apart j i eqn.symm), ?_, per⟩
  intro q hq
  apply mem q (hq.trans_le work)
  intro i eqn
  have index : (((histBase+i.val : ℕ) : Word w)).val = histBase+i.val :=
    Nat.mod_eq_of_lt ((Nat.add_lt_add_left i.isLt _).trans_le histFit)
  exact (hq.trans_le (low.trans (Nat.le_add_right _ _))).ne ((congrArg Fin.val eqn).trans index)

end PairSimulation.RefreshHook

end VPVNP
end Computability
end OAI
