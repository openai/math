import OAI.ThreeFlat.RAM.NavigationNodeFields

namespace OAI
/-! # Banks, loop controls and row caps of the native chronological publisher -/

namespace ThreeFlat.Diagonal.NavigationPass
open RAM.NavigationNodeRows

structure NodeArchive where
  banks : Banks
  headerBase : ℕ
  rawHeader : ℕ
  phase : ℕ
  counter : ℕ
  childCap : ℕ
  halfCap : ℕ
  motifCap : ℕ

end ThreeFlat.Diagonal.NavigationPass

end OAI
