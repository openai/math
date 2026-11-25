import OAI.ThreeFlat.RAM.TraceSuffixOracle

namespace OAI
/-! # Bounded native word arithmetic of the public suffix reader -/

namespace ThreeFlat.RAM.TraceSuffixOracle
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr DescriptorExpr
open scoped Fin.CommRing
variable {W : ℕ}

structure Bounds (W : ℕ) (s : Layout) (t : ℕ) : Prop where
  small : 11<2^W
  index : t<2^W
  width : s.hWidth<2^W
  paired : s.paired<2^W
  rawParams : s.rawParams<2^W
  rawTable : s.rawTable<2^W
  rawCount : s.rawCount<2^W
  code : s.codeBase+s.textSize<2^W
  description : s.description+s.textOffset+t<2^W
  parameters : s.parameters+t<2^W
  table : s.table+t<2^W

end ThreeFlat.RAM.TraceSuffixOracle

end OAI
