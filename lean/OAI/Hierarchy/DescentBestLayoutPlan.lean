import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # The two cost columns and the final strict layout comparison -/
namespace Hierarchy.DescentBestLayoutRAM
open ProtocolRAM
structure Banks where
  pairs : Bank
  tariff : Bool→Bank
  counts : Bool→ℕ
  starts : Bool→ℕ
  leftEnd : Bank
  rightEnd : Bank
  out : ℕ

variable (B : Banks)
def chooseLine : Expr := .branch .lt (.lookup B.rightEnd (.lit 0)) (.lookup B.leftEnd (.lit 0)) (.lit 1) (.lit 0)

end Hierarchy.DescentBestLayoutRAM

end OAI
