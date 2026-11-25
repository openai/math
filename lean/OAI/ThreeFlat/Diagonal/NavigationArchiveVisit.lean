import OAI.ThreeFlat.Diagonal.NavigationArchive
import OAI.ThreeFlat.Diagonal.PhysicalRecordFamily
import OAI.ThreeFlat.Diagonal.RefreshCursorLayout

namespace OAI
/-! # Mounted graph and width files for a chronological stage -/
namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM RAM NavigationDirectory PhysicalStage
variable {W : ℕ}

/-- The registers needed by an actual next physical call, including the complete numbered
state and the two immutable record spans allocated by the preceding pass. -/
structure Archive.Visit (a : Archive) (steps : List Stage) (edges : ℕ) (raw : ℕ→Bool)
    (cur : Word W) (pre : List Stage) {d l : ℕ} (X : State d l) (m : Memory W) : Prop where
  live : a.Live steps edges raw cur (finish a.K pre a.cursor) m
  graphLow : a.cursor.dense≤(finish a.K pre a.cursor).graph
  widthLow : a.cursor.dense≤(finish a.K pre a.cursor).width
  graphBound : (finish a.K pre a.cursor).graph+6*(Fintype.card X.Base*d)≤(finish a.K pre a.cursor).heap
  widthBound : (finish a.K pre a.cursor).width+X.edgeCount≤(finish a.K pre a.cursor).heap
  stored : SlotImage.Stored X.graph X.order (CompressorPacking.Native.tagOrdinal l)
    (RefreshStageNav.oldColumns (finish a.K pre a.cursor) (Fintype.card X.Base) d) (fun i=>(m i).val) X.width

theorem Archive.Visit.cast {a : Archive} {steps : List Stage} {edges : ℕ} {raw : ℕ→Bool} {cur : Word W}
    {pre : List Stage} {d l l' : ℕ} {X : State d l} {m : Memory W} (visit : a.Visit steps edges raw cur pre X m)
    (e : l=l') : a.Visit steps edges raw cur pre (e ▸ X : State d l') m := by cases e;exact visit

theorem Archive.Visit.redegree {a : Archive} {steps : List Stage} {edges : ℕ} {raw : ℕ→Bool} {cur : Word W}
    {pre : List Stage} {d d' l : ℕ} {X : State d l} {m : Memory W} (visit : a.Visit steps edges raw cur pre X m)
    (e : d=d') : a.Visit steps edges raw cur pre (e ▸ X : State d' l) m := by cases e;exact visit


end ThreeFlat.Diagonal.NavigationPass

end OAI
