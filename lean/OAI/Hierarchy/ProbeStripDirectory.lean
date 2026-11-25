import OAI.Hierarchy.ProbeStripDirectoryCore
import OAI.Hierarchy.ProbePayloadAccounts
import OAI.Hierarchy.ProbeStripAccounts
import OAI.Hierarchy.ProtocolRAMPurchaseMarketPorts
import OAI.Hierarchy.ProtocolRAMPurchaseInventory
import OAI.Hierarchy.ProtocolRAMOccurrenceHeader

namespace OAI
/-! # Addresses of actual strip commodities on the native inventory tape

The payload row supplies its source ordinal directly. A purchased row reads
the recorded DFS trajectory at the requested position. Only the stage and
signed-direction lane prefixes enter the immutable controller text. -/

noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage PurchaseFrozen
open scoped Fin.CommRing Classical

variable {w z N k H R d : ℕ}

theorem keySlot_read (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth : ℕ) (key : Key z d k) (m : Shelf.Mem z d) (data : sh.PortData S π depth key m)
    (room : (depth+1)*paths z S.degree depth ≤ 2^(Native.wordBits z d Native.copies))
    (i : PurchaseDirectory.Index (2^z) S.degree depth) (u : ChainStrip.Axes depth k)
    (p : Fin (2^z)) (hit : (Shelf.pathRows S π depth key i u.1).val = p.val) :
    (keySlot sh S depth key u).eval m (i.val:Word (Native.wordBits z d Native.copies)) =
      (PurchaseInventory.slot (.inr ((p,stage key),u.2)) : Word (Native.wordBits z d Native.copies)) :=
  keySlot_tiles sh S π depth key m data.tiles room i u p hit

end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
