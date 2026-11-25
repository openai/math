import OAI.ThreeFlat.Diagonal.RefreshGraphImage
import OAI.ThreeFlat.Diagonal.RefreshWidthImage
import OAI.ThreeFlat.Diagonal.SlotImageWrites

namespace OAI
/-! # The two refresh publication tables form a true source-indexed graph image -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.DescriptorScan CompressorPacking.Native
open RefreshDemandRows RefreshTies Expander
open scoped Fin.CommRing BigOperators

variable {W v a t h pad : ℕ} (current : Word W) (m : Memory W)

noncomputable def outputFields (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
    (E : SlotGraph (Fin (mPort a)) h) (hm : 2≤ mPort a) (pad : ℕ) (q : GraphRow v (mPort a) h pad) : Word W :=
  ((SlotImage.fields (CompressorRefresh.graph G E hm pad) finProdFinEquiv (tagOrdinal t) q.2 q.1.1 q.1.2:ℕ):Word W)

/-- The row enumerations used by the RAM publisher cover all six graph
fields and all numbered arc widths, including zero-width padding arcs. -/
theorem successor_image (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
    (E : SlotGraph (Fin (mPort a)) h) (hm : 2≤ mPort a) (C : SlotImage.Columns)
    (w : LiveSlot (Fin v) (BitWord t) (mPort a) (1+h+pad) → ℕ)
    (count : C.rows=v*mPort a*(1+h+pad))
    (separate : C.graph+6*C.rows≤C.widths ∨ C.widths+v*mPort a*(1+h+pad)*2^t≤C.graph)
    (bases : v*mPort a≤2^W) (degree : 1+h+pad≤2^W) (lanes : 2^t≤2^W) (bits : ∀ e,w e<2^W) :
    let graph := tableWord graphChart C.graph (outputFields G E hm pad)
    let widths := tableWord RefreshStageLayout.newWords C.widths (fun e=>(w e:Word W))
    SlotImage.Stored (CompressorRefresh.graph G E hm pad) finProdFinEquiv (tagOrdinal t) C
      (fun i=>(fillSegment C.widths (v*mPort a*(1+h+pad)*2^t) widths
        (fillSegment C.graph (6*(v*mPort a*(1+h+pad))) graph m) i).val) w := by
  intro graph widths
  rw [show 6*(v*mPort a*(1+h+pad))=6*C.rows by rw [count]]
  apply SlotImage.stored_after_fill _ _ _ _ _ m graph widths count separate bases degree lanes bits
  · intro p back f
    dsimp only [graph]
    rw [←graphChart_value C count ((back,f),p),tableWord_at]
    rfl
  · intro e
    have eq : SlotImage.edgeOrdinal finProdFinEquiv (tagOrdinal t) e=(RefreshStageLayout.newWords e).val := by
      rw [RefreshStageLayout.new_index]
      change (((e.1.1.2.val+mPort a*e.1.1.1.val)*(1+h+pad)+e.1.2.val)*2^t+(tagOrdinal t e.2).val)=_
      ac_rfl
    dsimp only [widths]
    rw [eq,tableWord_at]


end ThreeFlat.Diagonal.RefreshStageNav

end OAI
