import OAI.Computability.BorderVNP.PackedFinalCellSupplement
import OAI.Computability.BorderVNP.CellSparseExteriorBudget

/-! # The private RLE clock on the final owned, sorted cell and its real wiring -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalCell

open Filter Crossing Shortening CellSparse CellAddresses InheritedBank TeamScales DiagonalTallyCellReports
open RoutingISA RoutingISA.CompactMachine RoutingISA.TypedBatch VPVNP.BurstRAM
open scoped Classical
open private load from OAI.Computability.BorderVNP.PackedBankCellStatic

set_option maxHeartbeats 1800000

/-- Choose the stretching exponent before every public geometry, local sparse
source list and exterior assignment. The physically fetched RLE packet recovers
the sorted cell's exact signed contraction within both private machine limits. -/
theorem eventually_sparse_cell_with_wiring (T H B j R k : ℕ) (hH : 9 ≤ H) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ᶠ order : ℕ in atTop, ∀ r M E w Z high : ℕ,
      1 ≤ r → (r:ℝ) ≤ 2^((order:ℝ)^ω) → M ≤ width order (1/5) → E ≤ width order (1/4) →
      0 < w → w ≤ order → high.size+1 ≤ B*(logWidth r order+1)^j → 3*M+Z ≤ 4*(M+E+1)^3 →
      ∀ {D s m p : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
        (N : Network D P bits) (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m)
        (portID : P ↪ Fin p) (owner : Fin s → ℕ) (state : N.Site → Site) (c gadgets digits : ℕ) (field : SparseExterior.Field),
      (∀ v, owner (siteID v) = cell v) → (∀ v, (state v).incoming = incoming N v) →
      (∀ v, (state v).Schema) → load N cell state c false ≤ M → load N cell state c true ≤ M →
      gadgets ≤ M+1 → digits ≤ M+1 → digits ≤ R*(logWidth r order+1)^k → field.width+field.tail.length ≤ E → SparseExterior.Ordered field.width 0 field.spans →
      (∀ span ∈ field.spans, 0 < span.bits.length) →
      (∀ v ∈ sites siteID owner c, (state v).ScalarBound Z) →
      (∀ v ∈ sites siteID owner c, (state v).RowBound H) →
      (∀ v, (state v).TableBound T) → (∀ v, (state v).SplitFields (4*(M+E+1)^3) high) →
      ∀ extra : List Record, extra.length ≤ 2*(M+1) →
      (∀ rec ∈ extra, BottomReports.Wiring rec) → (∀ rec ∈ extra, Packet.RecordFields rec (4*(M+E+1)^3)) →
      let input := withWiring (cellInput N cell siteID edgeID portID owner state c gadgets digits field.values) extra
      let words := CompactFrame.pack w (Packet.input input.directory input.privateWires field.bytes)
      words.length ≤ width order (1/2) ∧ SparseExterior.clock w input.directory input.privateWires field ≤ order^25 ∧
        ∑ o ∈ choices SparseExterior.driver order words, o.2.value = input.weight := by
  obtain ⟨ω,hω,hcell⟩ := SparseExterior.eventually_private_cell 3076 T (B+10) (j+1) H R k
  refine ⟨ω,hω,?_⟩
  filter_upwards [hcell,eventually_ge_atTop 1] with order hclock hn
  intro r M E w Z high hr hrω hM hE hw hwn hhigh hz D s m p P inst bits N cell siteID edgeID portID owner state
    c gadgets digits field howner hin hschema hpub hexp hg hd hdigits hext horder hpos hscalar hrows htables hfactors
    extra hlen hextra hfields
  let input := withWiring (cellInput N cell siteID edgeID portID owner state c gadgets digits field.values) extra
  have format := wiring_clock_format hn hr hH hM hE hhigh hz N cell siteID edgeID portID owner state c gadgets
    digits field.values howner hin hschema hpub hexp hg hd hdigits hscalar hrows htables hfactors extra hlen hextra hfields
  have result := hclock r M E w input.privateWires _ hr hrω hM hE hw hwn input.directory field hext horder hpos
    format.static format.compact format.records format.reports format.mass format.raw format.rawDigits
    format.format format.tables format.digits
  exact ⟨result.1,result.2,SparseExterior.cell_value input.directory input.privateWires field hw format.widths result.2⟩

open BottomReports

/-- The genuine source bundles determine the copied row count, the count/use
tail and the final sparse packet. The physically fetched word cap and full
signed private clock follow from the original factors and cell loads. -/
theorem eventually_sparse_supplemented_cell (T H B j R k : ℕ) (hH : 9 ≤ H) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ᶠ order : ℕ in atTop, ∀ r M E w Z high : ℕ,
      1 ≤ r → (r:ℝ) ≤ 2^((order:ℝ)^ω) → M ≤ width order (1/5) → E ≤ width order (1/4) →
      0 < w → w ≤ order → high.size+1 ≤ B*(logWidth r order+1)^j → 3*M+Z ≤ 4*(M+E+1)^3 →
      ∀ {D s m p : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
        (N : Network D P bits) (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m)
        (portID : P ↪ Fin p) (owner : Fin s → ℕ) (state : N.Site → Site) (c gadgets digits : ℕ) (field : SparseExterior.Field),
      (∀ v, owner (siteID v) = cell v) → (∀ v, (state v).incoming = incoming N v) →
      (∀ v, (state v).Schema) → load N cell state c false ≤ M → load N cell state c true ≤ M →
      gadgets ≤ M+1 → digits ≤ M+1 → digits ≤ R*(logWidth r order+1)^k →
      SparseExterior.Ordered field.width 0 field.spans → (∀ span ∈ field.spans, 0 < span.bits.length) →
      (∀ v ∈ sites siteID owner c, (state v).ScalarBound Z) →
      (∀ v ∈ sites siteID owner c, (state v).RowBound H) →
      (∀ v, (state v).TableBound T) → (∀ v, (state v).SplitFields (4*(M+E+1)^3) high) →
      ∀ bundles : List Bundle, (bundles.map (fun x => count x.factors)).sum + bundles.length ≤ 2*(M+1) →
      field.width = suppliedSize N cell c → field.tail.length = gadgets*digits+(bundles.map Bundle.useBits).sum →
      field.width+field.tail.length ≤ E →
      (∀ x ∈ bundles, count x.factors ≤ x.header.cap ∧ x.header.copies ≤ 4*(M+E+1)^3 ∧
        x.header.boxBase+x.header.orig+x.header.cap ≤ 4*(M+E+1)^3) →
      let start := countBase N cell state c + gadgets*digits
      let input := withWiring (cellInput N cell siteID edgeID portID owner state c gadgets digits field.values)
        (supplements start bundles)
      let words := CompactFrame.pack w (Packet.input input.directory input.privateWires field.bytes)
      words.length ≤ width order (1/2) ∧ SparseExterior.clock w input.directory input.privateWires field ≤ order^25 ∧
        ∑ o ∈ choices SparseExterior.driver order words, o.2.value = input.weight := by
  obtain ⟨ω,hω,valid⟩ := eventually_sparse_cell_with_wiring T H B j R k hH
  refine ⟨ω,hω,?_⟩
  filter_upwards [valid] with order bound
  intro r M E w Z high hr hrω hM hE hw hwn hhigh hz D s m p P inst bits N cell siteID edgeID portID owner state
    c gadgets digits field howner hin hschema hpub hexp hg hd hdigits ord pos hscalar hrows htables hfactors
    bundles hsum supplied tail extent hboxes
  have total : suppliedSize N cell c+gadgets*digits+(bundles.map Bundle.useBits).sum ≤ E := by omega
  have checks := supplement_resources N state cell hin hexp bundles hsum total hboxes
  exact bound r M E w Z high hr hrω hM hE hw hwn hhigh hz N cell siteID edgeID portID owner state
    c gadgets digits field howner hin hschema hpub hexp hg hd hdigits extent ord pos hscalar hrows htables hfactors
    (supplements (countBase N cell state c+gadgets*digits) bundles) checks.1 checks.2.1 checks.2.2

end Packing.Inherited.FinalCell

end BorderVNP
end Computability
end OAI
