import OAI.Hierarchy.ProtocolRAMPreparedFrame
import OAI.Hierarchy.ProtocolRAMPostWriteFloor
import OAI.Hierarchy.ProtocolRAMNativePricedChart

namespace OAI
/-! # Retention of the outer market's actual row through its priced commit -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseFrozen PurchaseStage PurchaseCT
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {z d k q goods r edges : ℕ}

/-- Post-test, accepted histogram and commit outputs all follow the market's
physical rows. This applies also to a word *inside* this event's DFS workspace. -/
theorem priced_preserves_market (c : Mesh) (s : ℝ) (prices : PhasePrice)
    (F : Attempt→Format z d k q goods) (feeds : Boundary→List CommodityColumn) (sink : Sink r edges)
    (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr) (a : Attempt)
    (m : Shelf.Mem z d) (x : ℕ) (early : x<(F a).testsStart) :
    let C:=pricedInstalled c s prices F feeds sink idBase role ids
    ready C (.attempt a) m → after C (.attempt a) m x=prepared C a m x := by
  intro C head
  let L := C.layout a
  let B := repair C a
  let p := F a
  change x < p.testsStart at early
  have mask : x<p.maskStart := by change x<p.testsStart+1+_+_+_;omega
  have col (i : ℕ) : x<PostLayout.column p.maskStart p.indexBits L.candidates i := by
    exact mask.trans_le ((((Nat.le_add_right p.maskStart (2 ^ p.indexBits)).trans
      (Nat.le_add_right _ L.candidates)).trans (Nat.le_add_right _ 2)).trans
      (Nat.le_add_right _ (i * L.candidates)))
  have every : ∀t∈writes L B,x<t.out := writes_after L B x (col _) (col _) (col _) (fun _=>col _)
    (fun _=>col _) (fun _=>col _) (fun _=>col _) (fun _=>col _)
  refine after_prepared C a m x head (by change x<p.testsStart+1;omega) (by change x<p.testsStart+1+_+1;omega)
    (by change x<p.testsStart+1+_+1+_+1;omega) mask ?_ (col _) ?_
  · intro u hu
    rcases List.mem_cons.mp hu with rfl|hu
    · change x<p.maskStart+2^p.indexBits
      exact mask.trans_le (Nat.le_add_right _ _)
    · obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hu
      exact every t ht
  · apply StockCommit.priced_keeps
    · exact le_rfl
    · left
      change x<p.labelStart
      exact (col (PostLayout.columnsCount p.checkedBoard)).trans_le (Nat.le_add_right _ 1)

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
