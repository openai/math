import OAI.Computability.BorderVNP.CubeHostScatterPreparedColumns

/-! # The real physical cable numbering at a returning label and interval computation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.HostScatter

open Crossing Physical MeanChoice RoutingISA LocalRow NativeIntervals VPVNP.BurstRAM

variable {D w : ℕ} {P : Type*} {bits : P → ℕ} {C : Type} [Fintype C] [DecidableEq C]
variable {A : Type*} [Fintype A] {ar : CubeArena.Layout}
variable {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
variable {r z : Bank w} {m dir : Memory w} {events : List (TeamRAM.Event w)}

/-- The actual label and interval return supplies the intermediate RAM, interval
image, native cable endpoint bounds and physical edge order needed by the host. -/
theorem chooser_columns (N : Network D P bits) (cell : N.Site → C) (recv : A → C) (dataWidth : A → ℕ)
    (fit : LabelPrefixFits (pub 0).val w (readings m))
    (run : Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) r m events z dir) :
    let orig := readings m
    let frame := (pub 0).val
    let t := LabelIndex.layout frame orig
    let il := chooserLayout t frame (orig (frame+48)) (orig (frame+57)) (orig (frame+58))
    ∀ (cells : C ≃ Fin t.cells) (edges : N.CrossingEdge cell ↪ Fin t.cableCount) (data : A ↪ Fin t.deliveryCount)
      (positive : 0 < ar.header.d) (alphabet : ar.header.d^(ar.n+1) = t.labels),
      MeanChoice.RowPlacement (networkRows N cell recv dataWidth) (LabelIndex.fromTables t orig fit.endpoints)
        cells (edges.sumMap data) →
      t.deliveries+t.deliveryCount*7 ≤ il.labels → frame+112 ≤ t.cables →
      t.cables+3*t.cableCount ≤ ar.header.header → t.cells=ar.cells → t.cableCount ≤ ar.cables →
      il.labels=ar.publicBase → il.ordinals=ar.ordinalBase →
      ∃ before : Memory w, il.Image (readings before) il.count (readings dir) ∧ il.Fits w (readings before) ∧
        il.Fields (readings before) ∧ CableColumns ar frame il (readings before) ∧
        (∀ x < ar.publicBase, readings dir x = orig x) ∧
        ∃ (ord : N.CrossingEdge cell ≃ Fin (Fintype.card (N.CrossingEdge cell))) (row : Fin (Fintype.card (N.CrossingEdge cell)) ↪o Fin il.count),
          (∀ e, row (ord e) = edges e) ∧ NativeIntervals.PhysicalRows N cell il (readings before) ord row
            (cells.toEmbedding.trans Fin.valEmbedding) (meanPackedLabel N cell recv dataWidth ((List.finRange t.cells).map cells.symm) ar.n ar.header.d positive)
            (productCode ar.n ar.header.d il.alphabet alphabet) := by
  intro orig frame t il cells edges data positive alphabet placed dataEnd above below nCells cableBound lab ordinal
  obtain ⟨_,mid,before,_,_,chooser,interval⟩ := CellDispatch.seq_split run
  have chooserTrace := native_chooser_rows N cell recv dataWidth pub mac ar.n ar.header.d positive r m fit.endpoints cells
    edges data alphabet placed fit.allocated fit.cables dataEnd fit.heads (by have lo := fit.frame; have hi := fit.heads; omega) fit.means fit.envelope
  obtain ⟨_,u,m',canon,_,off,codes,ord,row,aligned,physical⟩ := chooserTrace
  obtain ⟨_,rfl,rfl⟩ := chooser.unique_of_deterministic (by decide) canon
  have keep (a : ℕ) (ha : a < il.labels) : readings before a = orig a := congrArg Fin.val (off a ha)
  have bound (i : Fin t.cells) : readings before (il.labels+i.val) < t.labels := by
    have pos := pow_pos positive (ar.n+1)
    have shape : ar.header.d^(ar.n+1)-1+1 = t.labels := by omega
    exact (codes i).trans_lt ((Physical.tableCodes t orig fit.endpoints (ar.header.d^(ar.n+1)-1) i).isLt.trans_le shape.le)
  have room := chooser_interval_fits t orig (readings before) frame il.labels il.widths il.ordinals w
    fit.endpoints keep bound fit.positive fit.cables fit.frame fit.widths fit.ordinals fit.space fit.envelope
  have field (j : ℕ) (hj : j ≤ 58) := keep (frame+j) (by have lo := fit.frame; change frame+58 < il.labels at lo; omega)
  have fields : il.Fields (readings before) := ⟨field 6 (by decide),field 7 (by decide),field 48 (by decide),field 56 (by decide),
    field 57 (by decide),field 58 le_rfl⟩
  obtain ⟨_,_,_,actual,_,_,img⟩ := run_prepare pub mac il mid before room rfl fields
  obtain ⟨_,_,rfl⟩ := interval.unique_of_deterministic (by decide) actual
  refine ⟨before,img,room,fields,⟨lab,ordinal,⟨above,below⟩,cableBound,?_⟩,?_,ord,row,aligned,physical⟩
  · intro i hi
    have old := fit.endpoints.cables i hi
    have cab := fit.cables
    change t.cables+t.cableCount*3 ≤ il.labels at cab
    have hs : il.src (readings before) i = (LabelIndex.cableAt t orig i).src := by
      change readings before (t.cables+3*i) = orig (t.cables+i*3)
      rw [Nat.mul_comm i 3,keep _ (by change i < t.cableCount at hi; omega)]
    have hd : il.dst (readings before) i = (LabelIndex.cableAt t orig i).dst := by
      change readings before (t.cables+3*i+1) = orig (t.cables+i*3+1)
      rw [Nat.mul_comm i 3,keep _ (by change i < t.cableCount at hi; omega)]
    exact ⟨hs ▸ nCells ▸ old.1,hd ▸ nCells ▸ old.2⟩
  · intro x hx
    have wi : il.labels+t.cells ≤ il.widths := fit.widths
    have oi : il.widths+t.labels^2 ≤ il.ordinals := fit.ordinals
    have lo : x < il.labels := lab ▸ hx
    exact (img.outside x (by omega) (by omega)).trans (keep x lo)

end Cube.HostScatter

end BorderVNP
end Computability
end OAI
