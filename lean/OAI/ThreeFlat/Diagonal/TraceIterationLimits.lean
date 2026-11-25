import OAI.ThreeFlat.Diagonal.NavigationArchiveDirectory

namespace OAI
/-! # Word and capacity bounds of a chronological directory -/

namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM NavigationDirectory

/-- Bounds on the actual packed scratch regions, independent of the guessed history. -/
structure Archive.TraceLimits {W : ℕ} (a : Archive) (limit : ℕ) (cur : Word W)
    (steps : List Stage) (edges cap : ℕ) : Prop where
  origin : a.cursor.header=a.seed+64
  tables : a.seed+(a.directory steps edges W).length≤a.cursor.dense
  raw : a.cursor.dense+a.histWords steps≤a.cursor.heap
  controls : a.cursor.heap+(steps.map Stage.heapWords).sum≤cur.val
  volume : (steps.map Stage.heapWords).sum≤limit
  capacity : W*a.histWords steps≤cap

end ThreeFlat.Diagonal.NavigationPass

end OAI
