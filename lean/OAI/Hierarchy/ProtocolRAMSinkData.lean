import OAI.Hierarchy.ProtocolRAMRouteSettlement

namespace OAI
/-! # The native settlement sink and its physical memory banks -/

namespace Hierarchy.ProtocolRAM.Calendar

structure Sink (r edges : ℕ) where
  banks : RouteSettlement.Banks
  source : ℕ
  table : ℕ
  destination : ℕ
  owners : Bank
  geometry : Fin 7→Expr

end Hierarchy.ProtocolRAM.Calendar

end OAI
