import OAI.ThreeFlat.Diagonal.CompressorNativeGraph

namespace OAI
/-! # The two geometries of a history party -/

namespace ThreeFlat.RAM.HistoryGatherBody
open Diagonal.CompressorPacking.Native

inductive Geometry
  | shrink (S : Graph.Stage)
  | refresh (ports degree padding : ℕ)

end ThreeFlat.RAM.HistoryGatherBody

end OAI
