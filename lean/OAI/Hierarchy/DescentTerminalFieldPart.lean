import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # One source column and its weighted lookup for the issued six-field record -/
namespace Hierarchy.DescentTerminalPrintedFieldsRAM
open ProtocolRAM

structure Part where
  source : Bank
  weights : Bank

def Part.fetch (x : Part) : Expr := .lookup x.weights (.lookup x.source .row)

end Hierarchy.DescentTerminalPrintedFieldsRAM

end OAI
