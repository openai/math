import OAI.Hierarchy.ProtocolRAMPurchaseOwners
import OAI.Hierarchy.ProtocolRAMGeneratedWriteCheap

namespace OAI
/-! # Cheap native opcodes for constructing the input-socket owner table -/

namespace Hierarchy.ProtocolRAMPurchaseOwners
open ProtocolRAM

theorem cheap (w n groups m scratch : ℕ) (x : Columns) :
    CheapCode (program w n groups m scratch x) :=
  cheap_seq (scan_cheap w x.owner.base (groups*m) (.lit 0))
    (ProtocolRAMRankCheap.generated w scratch (scratch+n) n (addressExpr x) rowCode)

end Hierarchy.ProtocolRAMPurchaseOwners

end OAI
