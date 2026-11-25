import OAI.Computability.BorderVNP.FiniteProfileSlottedNetwork
import OAI.Computability.BorderVNP.PackedRoutingChooserHeader
import OAI.Computability.BorderVNP.PackedDirectoryRowFields

/-! # The actual label chooser on a published finite-field directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction ProcessorSlots
open PackedHistoryCircuit Packing RoutingOutputs Crossing CellAddresses CellAddressCircuit CellAddressPhysical
open Packing.Directory BorderVNP.Cube Cube.Physical Cube.MeanChoice Cube.LabelIndex
open scoped Classical

variable {w : ℕ}

/-- Every occupied natural descriptor from the slotted writer is encoded
without wrapping, by its own real key and the size of that key's cell. -/
theorem slotted_row_words {a : CubeArena.Layout} {D : Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {pins : Pins.Layout} {pub : Arg → Word w} {mid : Memory w} {base : ℕ}
    {I : Type*} [Fintype I] {cell : I → Fin a.cells} {id : I ↪ ℕ} {width : I → ℕ}
    (write : SlottedWriter a D pp lp pins pub mid base cell id width)
    (teams : D.teams ≤ 2^w) (procs : D.processors ≤ 2^w) (fields : D.fields ≤ 2^w)
    (literal : D.literal<2^w) (cells : a.cells ≤ 2^w) (stride : a.cellStride ≤ 2^w) :
    ∀ i : Fin (D.directory pp lp).length,∀ j ∈ (D.directory pp lp)[i.val].words,j<2^w := by
  apply D.populated_words_fit_of_slabs pp lp write.destinations write.fields write.tailRoom teams procs fields literal
  · intro key
    rw [write.placement.entry]
    exact (cell (write.placement.key key)).isLt.trans_le cells
  · intro key
    rw [write.placement.entry,←write.placement.width_eq]
    exact (DataSlabs.base_end_le cell id width (write.placement.key key)).trans ((write.slabs _).trans stride)

/-- The public cells, cable endpoints and receiving rows read by the
actual chooser after publication. The equivalence of cell IDs is the
canonical cast by the computed count, so separate exterior runs can use it. -/
theorem slotted_label_placement {D s t d k b : ℕ} {P σ : Type*} [Fintype P] [Fintype σ] {bits : P → ℕ}
    (a : CubeArena.Layout) (dir : Directory.Layout) (N : Network D P bits) (cell : N.Site → Fin a.cells)
    (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin a.cables) (portID : P ↪ Fin t)
    (F : Fields s a.cables t a.cells d k b σ) (x : σ → Bool)
    (net : Represents N cell aux siteID edgeID portID F x) (ids : ∀ c,(F.cells c).val=c.val)
    (wireFit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (hk : k ≤ b) (widthFit : b ≤ w) (positive : 0<a.cells)
    (original : Fin dir.entries → N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (liveWidth : ∀ j,bits (live j)=dir.block)
    (pub : Arg → Word w) (base origin gap : ℕ) (before mid : Memory w) :
    let head := (pub 0).val
    let h := privateLayout head origin a.cables a.cells dir.entries dir.description gap
    let tables := bases origin a.cables a.cells dir.entries
    let pp := ISA.placement (readings mid) h.raw
    let lp := ISA.placement (readings mid) tables.livePairs
    let rows := dir.directory pp lp
    let m := readings (ISA.publish mid head base rows)
    let l := LabelIndex.layout head m
    ∀ {I : Type*} [Fintype I] {sc : I → Fin a.cells} {sid : I ↪ ℕ} {sw : I → ℕ} {pins},
    SlottedWriter a dir pp lp pins pub mid base sc sid sw →
    Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings before) →
    h.Image (readings before) dir.entries (readings mid) → h.Fits w (readings before) →
    Header head origin a.cables a.cells dir.entries (readings before) →
    base+7*dir.candidates ≤ origin → origin < 2^w →
    dir.teams ≤ 2^w → dir.processors ≤ 2^w → dir.fields ≤ 2^w → dir.literal<2^w →
    a.cells ≤ 2^w → a.cellStride ≤ 2^w →
    ∃ (count : l.cells=a.cells) (ep : Endpoints l m) (edges : N.CrossingEdge cell ↪ Fin l.cableCount)
      (del : Fin rows.length ≃ Fin l.deliveryCount) (recv : Fin rows.length → Fin a.cells),
      (∀ i, (recv i).val=rows[i.val].cell) ∧
      RowPlacement (networkRows N cell recv (fun i => rows[i.val].width)) (fromTables l m ep)
        (finCongr count.symm) (edges.sumMap del.toEmbedding) := by
  intro head h tables pp lp rows m l I _ sc sid sw pins write img placed fit headWords span hi
    teams procs fields literal cells stride
  have num : rows.length ≤ dir.candidates := dir.directory_length_le pp lp
  have low := write.rawStart
  change head+112 ≤ base at low
  have early : head+11 < origin := by omega
  have src : readings before (head+8)=base :=
    (private_before_ends placed _ (by dsimp [bases]; omega)).symm.trans write.pointers.1
  obtain ⟨ca,cc,de,rc,cn⟩ := chooser_header (readings before) mid rows headWords src early (by omega) placed (by omega)
  change l.cables=origin at ca
  change l.cableCount=a.cables at cc
  change l.deliveries=base at de
  change l.deliveryCount=rows.length at rc
  change l.cells=a.cells at cn
  let named : LabelIndex.Layout := {l with cables:=origin,cableCount:=a.cables,deliveries:=base,deliveryCount:=rows.length,cells:=a.cells}
  have same : named=l := by dsimp only [named]; rw [←ca,←cc,←de,←rc,←cn]
  obtain ⟨recv,atCell,ep,del,matchRows⟩ := after_private_placement named N cell aux siteID edgeID portID F x net ids
    wireFit hk widthFit positive dir original live liveWidth write.destinations head gap (readings before) mid
    img placed fit rfl (by change head+9<origin; omega) (by change head+9<base; omega)
    (Or.inr (by change base+7*rows.length ≤ origin; omega)) (slotted_row_words write teams procs fields literal cells stride)
  let witness (v : LabelIndex.Layout) := ∃ (count : v.cells=a.cells) (ep : Endpoints v m)
    (edges : N.CrossingEdge cell ↪ Fin v.cableCount) (del : Fin rows.length ≃ Fin v.deliveryCount)
    (recv : Fin rows.length → Fin a.cells), (∀ i, (recv i).val=rows[i.val].cell) ∧
      RowPlacement (networkRows N cell recv (fun i => rows[i.val].width)) (fromTables v m ep)
        (finCongr count.symm) (edges.sumMap del.toEmbedding)
  exact (congrArg witness same).mp ⟨rfl,ep,CableTriples.wireOrd N cell edgeID,del,recv,atCell,matchRows⟩

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
