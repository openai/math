import OAI.ThreeFlat.Diagonal.PhysicalTreeResources
import OAI.ThreeFlat.Diagonal.PhysicalRunCharges
import OAI.ThreeFlat.Diagonal.PhysicalBlockSchedule
import OAI.ThreeFlat.Diagonal.HistoryPhysicalStages
import OAI.ThreeFlat.Diagonal.CompressorHalfPorts
import OAI.ThreeFlat.Diagonal.ShrinkTableOrdinal

namespace OAI
/-! # Finite tile prices and the incident width of every native port layout -/

namespace ThreeFlat.Diagonal.PhysicalStage.Block
open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression Expander CompressorPacking HistoryContraction MotifOuterTerms
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F] [Fintype F] (B : Block F)

/-- Structural resources of each actual fixed shrink tile, before multiplying
by its true copy count and sorter height. -/
def shrinkTilePrice (i : Fin (B.shrink.more.length+1)) :=
  let tile:=B.shrink.block (B.shrink.row i)
  Tree.tileTariff demandGraph supplyGraph (B.shrink.base (B.shrink.row i))
    tile.bits (Fintype.card tile.Alphabet) tile.bitCap

def refreshTilePrice (i : Fin (B.refresh.last+1)) (j : Fin (2^B.exponent B.levels)) :=
  let tile:=B.refresh.block i
  let G:=DoublePorts.connectedSupply B.graph B.hh B.degree B.symmetric B.connected
  1+Tree.portTariff (RefreshMotif.denseGraph _) (ports G) (B.refresh.base i)
    tile.bits (Fintype.card tile.Alphabet) tile.bitCap j

def shrinkPrice := ∑ i,B.shrinkTilePrice i
def refreshPrice := ∑ i,∑ j,B.refreshTilePrice i j
/-- Capacity of the shrink incident directory at this level. -/
def shrinkMotifCap (i : Fin B.levels) : ℕ :=
  let d := 2^B.exponent i.val
  8*d^2*2^(2*d+1)

def motifCap := ∑ i : Fin B.levels,B.shrinkMotifCap i

/-- The one local coefficient needed for both actual geometric move kinds.
Its indices are finite entries of the original block, independent of age. -/
def localCoefficient :=
  (2+(1+B.motifCap+2*B.shrinkPrice*(B.motifCap+1)))+(2+B.refreshPrice)

omit [Fintype F] in
theorem shrink_tile_price (i : Fin (B.shrink.more.length+1)) : B.shrinkTilePrice i≤B.shrinkPrice :=
  Finset.single_le_sum (fun j _=>Nat.zero_le (B.shrinkTilePrice j)) (Finset.mem_univ i)

omit [Fintype F] in
theorem refresh_tile_price (i : Fin (B.refresh.last+1)) (j : Fin (2^B.exponent B.levels)) :
    B.refreshTilePrice i j≤B.refreshPrice := by
  have inside : B.refreshTilePrice i j≤∑ k,B.refreshTilePrice i k :=
    Finset.single_le_sum (fun k _=>Nat.zero_le (B.refreshTilePrice i k)) (Finset.mem_univ j)
  exact inside.trans (Finset.single_le_sum (fun t _=>Nat.zero_le (∑ k,B.refreshTilePrice t k)) (Finset.mem_univ i))

omit [Fintype F] in
theorem shrink_local_coefficient (i : Fin B.levels) :
    (2+(1+B.shrinkMotifCap i+2*B.shrinkPrice*(B.shrinkMotifCap i+1)))≤B.localCoefficient := by
  have cap : B.shrinkMotifCap i≤B.motifCap:=
    Finset.single_le_sum (fun j _=>Nat.zero_le (B.shrinkMotifCap j)) (Finset.mem_univ i)
  have scale:=Nat.mul_le_mul_left (2*B.shrinkPrice) (Nat.succ_le_succ cap)
  exact (Nat.add_le_add_left (Nat.add_le_add (Nat.add_le_add_left cap 1) scale) 2).trans
    (Nat.le_add_right _ (2+B.refreshPrice))

omit [Fintype F] in
theorem refresh_local_coefficient : 2+B.refreshPrice≤B.localCoefficient:=Nat.le_add_left ..

omit [Fintype F] in
/-- The real prior incidence widths and site's copies pay the original
shrink/refresh structural tariff against the true chronological push. -/
theorem local_cost_to_push {α : Type*} [Fintype α] (prev widths : α→ℕ)
    (fresh copied newWidth actual coefficient height W : ℕ)
    (previous : ∀ x,widths x≤prev x) (localCharge : 1+newWidth+copied≤fresh)
    (heightFit : height≤W) (shape : coefficient≤B.localCoefficient)
    (compiled : actual≤coefficient*(height+1)^3*(1+((∑ x,widths x)+newWidth)+copied)) :
    actual≤(B.localCoefficient*(W+1)^3)*(fresh+∑ x,prev x) := by
  have before:=Finset.sum_le_sum (s:=Finset.univ) fun x _=>previous x
  have weights : 1+((∑ x,widths x)+newWidth)+copied≤fresh+∑ x,prev x:=by omega
  exact compiled.trans (Nat.mul_le_mul (Nat.mul_le_mul shape (Nat.pow_le_pow_left (Nat.succ_le_succ heightFit) 3)) weights)

end
end ThreeFlat.Diagonal.PhysicalStage.Block

namespace ThreeFlat.Diagonal.PhysicalStage
open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression CompressorPacking HistoryContraction
open scoped Classical BigOperators
noncomputable section

/-- Port order is a permutation of the outgoing and incoming halves of the native graph. -/
theorem State.words_incidentWidth {d l : ℕ} (A : State d l) {Pins : Type} (L : A.Words Pins) (v : A.Site) :
    L.ports.halfBits v=A.incidentWidth v := by
  obtain ⟨z,rfl⟩ := A.chart.surjective v
  let ord := Native.ShrinkStage.Halves.portOrder A.graph A.chart z
  let width := fun a : A.shape.graph.Port (A.chart z) => A.width a.val.1
  calc
    _ = ∑ a : A.shape.graph.Port (A.chart z),width a := (L.order (A.chart z)).sum_comp width
    _ = ∑ i : Fin (2*d),width (ord i) := (ord.sum_comp width).symm
    _ = ∑ i : Fin (2*d),A.width (Native.ShrinkStage.Halves.sourceHalf A.graph z i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun q => A.width (Prod.fst q)) (Native.ShrinkStage.Halves.portOrder_value A.graph A.chart z i)
    _ = _ := by
      have arc (i : Fin d) : A.siteArc (A.chart z,i)=((z.1,i),z.2) := by
        change (((A.chart.symm (A.chart z)).1,i),(A.chart.symm (A.chart z)).2)=_
        rw [A.chart.symm_apply_apply]
      simpa only [State.incidentWidth, arc] using half_total A.graph A.width z

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
