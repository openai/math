import OAI.Computability.BorderVNP.PackedScheduledSparseCell
import OAI.Computability.BorderVNP.DiagonalNativeOwnedCellInputs

/-! # Resource bounds for the actually placed sparse call -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalCell

open Filter Crossing Shortening CellSparse CellAddresses InheritedBank TeamScales BottomReports
open RoutingISA RoutingISA.CompactMachine RoutingISA.TypedBatch VPVNP.BurstRAM
open scoped Classical
open private load from OAI.Computability.BorderVNP.PackedBankCellStatic

/-- The native task that restored this augmented logical cell satisfies both
the word bound on the physical burst and the interpreter's time bound
on every sampled digit. -/
theorem scheduled_placed_call {order r M E w Z high T H B j R k : ℕ}
    (scheduled : Diagonal.SparseCellBudgetAt 3076 T (B+10) (j+1) H R k order r)
    (hn : 1 ≤ order) (hr : 1 ≤ r) (hH : 9 ≤ H) (hM : M ≤ TeamScales.width order (1/5))
    (hE : E ≤ TeamScales.width order (1/4)) (hw : 0<w) (hwn : w≤order)
    (hhigh : high.size+1 ≤ B*(logWidth r order+1)^j) (hz : 3*M+Z ≤ 4*(M+E+1)^3)
    {D s m p : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m)
    (portID : P ↪ Fin p) (owner : Fin s → ℕ) (state : N.Site → Site) (c gadgets digits : ℕ)
    (field : SparseExterior.Field)
    (howner : ∀ v, owner (siteID v)=cell v) (hin : ∀ v, (state v).incoming=incoming N v)
    (hschema : ∀ v, (state v).Schema) (hpub : load N cell state c false ≤ M) (hexp : load N cell state c true ≤ M)
    (hg : gadgets ≤ M+1) (hd : digits ≤ M+1) (hdigits : digits ≤ R*(logWidth r order+1)^k)
    (hord : SparseExterior.Ordered field.width 0 field.spans) (hpos : ∀ span ∈ field.spans, 0 < span.bits.length)
    (hscalar : ∀ v ∈ sites siteID owner c, (state v).ScalarBound Z)
    (hrows : ∀ v ∈ sites siteID owner c, (state v).RowBound H) (htables : ∀ v, (state v).TableBound T)
    (hfactors : ∀ v, (state v).SplitFields (4*(M+E+1)^3) high)
    (bundles : List Bundle) (hsum : (bundles.map (fun x => count x.factors)).sum+bundles.length ≤ 2*(M+1))
    (supplied : field.width = suppliedSize N cell c) (tail : field.tail.length = gadgets*digits+(bundles.map Bundle.useBits).sum)
    (extent : field.width+field.tail.length ≤ E) (hboxes : ∀ x ∈ bundles,
      count x.factors ≤ x.header.cap ∧ x.header.copies ≤ 4*(M+E+1)^3 ∧ x.header.boxBase+x.header.orig+x.header.cap ≤ 4*(M+E+1)^3)
    {Origin : Type} (placed : CellPacket.Placed Origin) (extra : List Record)
    (read : SparseExterior.logicalCell placed extra field =
      withWiring (cellInput N cell siteID edgeID portID owner state c gadgets digits field.values)
        (supplements (countBase N cell state c+gadgets*digits) bundles)) :
    let input := SparseExterior.logicalCell placed extra field
    (CompactFrame.pack w (Packet.input input.directory input.privateWires field.bytes)).length ≤ TeamScales.width order (1/2) ∧
      input.directory.ProfileWidths ∧ SparseExterior.clock w input.directory input.privateWires field ≤ order^25 := by
  intro input
  have bound := scheduled_sparse_cell scheduled hn hr hH hM hE hw hwn hhigh hz N cell siteID edgeID portID owner state
    c gadgets digits field howner hin hschema hpub hexp hg hd hdigits hord hpos hscalar hrows htables hfactors
    bundles hsum supplied tail extent hboxes
  have base := directory_profileWidths owner N cell siteID edgeID portID state c
    (DiagonalTallyCellReports.countFields (countBase N cell state c) gadgets digits) (fun v _ => hschema v)
  dsimp only [input]
  rw [read]
  refine ⟨bound.1,?_,bound.2.1⟩
  intro row hr
  rcases List.mem_append.mp hr with rowOld | rowNew
  · exact base row rowOld
  · exact wiring_profile (supplements_wiring _ bundles row rowNew)

end Packing.Inherited.FinalCell

end BorderVNP
end Computability
end OAI
