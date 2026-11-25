import OAI.ThreeFlat.Diagonal.NavigationArchiveDirectory

namespace OAI
/-! # The addresses of the trace verifier's mounted sector -/

namespace Hierarchy.TraceAdmission
open ThreeFlat.Diagonal.NavigationPass

/-- The disjoint arrays used by the chronological verifier, in word addresses
relative to the start of its mounted sector. -/
structure ArchivePlacement (a : Archive) (β w : ℕ) : Prop where
  seed : a.seed=β
  header : a.cursor.header=β+64
  dense : a.cursor.dense=β+(2^w)^4
  graph : a.cursor.graph=β+2*(2^w)^4
  width : a.cursor.width=β+3*(2^w)^4
  records : a.initialRecords=β+4*(2^w)^4
  heap : a.cursor.heap=β+5*(2^w)^4
  control : a.control=β+6*(2^w)^4
  node : a.cursor.node=0

end Hierarchy.TraceAdmission

end OAI
