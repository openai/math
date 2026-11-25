import OAI.ThreeFlat.RAM.HistoryNodeFromSite
import OAI.Hierarchy.GridPinReceiverPrefix
import OAI.Hierarchy.FactorPinPrefix
import OAI.Hierarchy.HistorySelectedPublisher

namespace OAI
/-! # Every selected original endpoint has its actual sparse tick address -/

namespace Hierarchy.HistorySelectedSeed
open FactorPinIntervals GridThrough Computability.VPVNP.BurstRAM
open scoped Fin.CommRing
open ThreeFlat
open RAM.HistoryStageBody.Physical Diagonal.PhysicalStage

variable {T : Type} {S N d span b : ℕ} (Q : Layout T S N d)

private theorem original_bucket (h : 0< span) (i : Fin (bucketLength S span b)) :
    (blockBit S span b i).val/span=b := by
  apply (blockBits_mem h _).mp
  exact List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩

/-- Even the clipped last interval is contiguous within its original factor. -/
theorem slots_consecutive (positive : 0< span) (nonempty : 0<bucketLength S span b)
    (owner : ℕ→Fin N) (source : ∀j:Fin S,Q.origin j=owner (j.val/span))
    (i : Fin (bucketLength S span b)) :
    (Q.slot (blockBit S span b i)).val =
      (Q.slot (blockBit S span b ⟨0,nonempty⟩)).val+i.val := by
  let f := fun j : Fin (bucketLength S span b)=>(Q.slot (blockBit S span b j)).val
  have chain (a) (h : a<bucketLength S span b) : f ⟨a,h⟩=f ⟨0,nonempty⟩+a := by
    induction a with
    | zero => simp
    | succ a ih =>
      let j : Fin (bucketLength S span b):=⟨a,by omega⟩
      let k : Fin (bucketLength S span b):=⟨a+1,h⟩
      have same : Q.origin (blockBit S span b j)=Q.origin (blockBit S span b k) := by
        rw [source,source,original_bucket positive j,original_bucket positive k]
      have step := Q.slot_adjacent (a:=blockBit S span b j) (b:=blockBit S span b k)
        (show b*span+(a+1)=(b*span+a)+1 by omega) same
      change f k=f j+1 at step
      have old := ih j.isLt
      change f j=f ⟨0,nonempty⟩+a at old
      change f k=f ⟨0,nonempty⟩+(a+1)
      omega
  exact chain i.val i.isLt

variable {F Pins E : Type} [Field F] {m q k n W : ℕ}

/-- The node used for billing and the actually emitted six-word cache header
have the same gate tree and endpoint numbering when its selected source is
this native interval. -/
theorem node_eq (z : Run.SelectedNode F Pins E) (pointer : E→ℕ) (slot stream ends : ℕ)
    (atPin : ∀ i,pointer (z.origin i)=2+slot+i.val) :
    NodeValue.ofSite z pointer stream ends = node z.net z.external slot stream ends := by
  unfold NodeValue.ofSite node
  congr 1
  funext i
  exact atPin i

theorem pointer_at {lanes : ℕ} (Q : Layout (Cell k n×Fin q) S N d)
    (owner : ℕ→Fin N) (source : ∀j:Fin S,Q.origin j=owner (j.val/span))
    (pos : 0< span) (lane : Fin lanes) (active : 0<bucketLength S span lane.val)
    (receiver : Memory W) (intervals : ℕ) (room : d≤2^W)
    (offset : receiver (intervals+4*lane.val+3)=
      ((Q.slot (blockBit S span lane.val ⟨0,active⟩)).val:Word W))
    (i : Fin (bucketLength S span lane.val)) :
    2+(Q.slot (blockBit S span lane.val i)).val =
      2+(receiver (intervals+4*lane.val+3)).val+i.val := by
  rw [offset,Fin.val_cast_of_lt ((Q.slot _).isLt.trans_le room),
    slots_consecutive Q pos active owner source i]
  omega

end Hierarchy.HistorySelectedSeed

end OAI
