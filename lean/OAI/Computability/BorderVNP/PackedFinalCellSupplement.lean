import OAI.Computability.BorderVNP.PackedFinalCellClock

/-! # The true supplemented private call on the owner-sorted final cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalCell

open Filter Crossing Shortening CellSparse CellAddresses InheritedBank TeamScales BottomReports
open RoutingISA RoutingISA.CompactMachine RoutingISA.TypedBatch VPVNP.BurstRAM
open scoped Classical
open private load from OAI.Computability.BorderVNP.PackedBankCellStatic

set_option maxHeartbeats 1800000
set_option maxRecDepth 18000

/-- The real supplemental source cursor stays in the cubic compact-field range.
The number and format of the added rows come directly from the original factors. -/
theorem supplement_resources {D M E c gadgets digits : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (state : N.Site → Site) (cell : N.Site → ℕ)
    (hin : ∀ v, (state v).incoming = incoming N v) (hexp : load N cell state c true ≤ M)
    (bundles : List Bundle) (hsum : (bundles.map (fun x => count x.factors)).sum+bundles.length ≤ 2*(M+1))
    (htail : suppliedSize N cell c+gadgets*digits+(bundles.map Bundle.useBits).sum ≤ E)
    (hboxes : ∀ x ∈ bundles, count x.factors ≤ x.header.cap ∧ x.header.copies ≤ 4*(M+E+1)^3 ∧
      x.header.boxBase+x.header.orig+x.header.cap ≤ 4*(M+E+1)^3) :
    let extra := supplements (countBase N cell state c+gadgets*digits) bundles
    extra.length ≤ 2*(M+1) ∧ (∀ rec ∈ extra, Wiring rec) ∧ (∀ rec ∈ extra, Packet.RecordFields rec (4*(M+E+1)^3)) := by
  intro extra
  let start := countBase N cell state c + gadgets*digits
  let V := 4*(M+E+1)^3
  have hbank := (merged_bank_capacity N state cell c hin).trans (Nat.mul_le_mul_left 3 hexp)
  have hp : privateBits N cell state c ≤ 3*M := (Nat.le_add_right _ _).trans hbank
  have hc : M+E+1 ≤ (M+E+1)^3 := Nat.le_self_pow (by decide) _
  have hend : nextCursor start bundles ≤ V := by
    change privateBits N cell state c + suppliedSize N cell c + gadgets*digits + (bundles.map Bundle.useBits).sum ≤
      4*(M+E+1)^3
    omega
  exact ⟨(supplements_length start bundles).trans_le hsum,supplements_wiring start bundles,
    supplements_recordFields start bundles V (by dsimp only [V]; omega) hend hboxes⟩

/-- The actual copied original factors determine the number of supplemental
records, the cursor increments, and the final typed packet. Its fixed native
clock and signed value follow from the genuine bundle bounds. -/
theorem eventually_supplemented_cell (T H B j R k : ℕ) (hH : 9 ≤ H) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ᶠ order : ℕ in atTop, ∀ r M E w Z high : ℕ,
      1 ≤ r → (r:ℝ) ≤ 2^((order:ℝ)^ω) → M ≤ width order (1/5) → E ≤ width order (1/4) →
      0 < w → w ≤ order → high.size+1 ≤ B*(logWidth r order+1)^j → 3*M+Z ≤ 4*(M+E+1)^3 →
      ∀ {D s m p : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
        (N : Network D P bits) (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m)
        (portID : P ↪ Fin p) (owner : Fin s → ℕ) (state : N.Site → Site) (c gadgets digits : ℕ) (external : List Bool),
      (∀ v, owner (siteID v) = cell v) → (∀ v, (state v).incoming = incoming N v) →
      (∀ v, (state v).Schema) → load N cell state c false ≤ M → load N cell state c true ≤ M →
      gadgets ≤ M+1 → digits ≤ M+1 → digits ≤ R*(logWidth r order+1)^k → external.length ≤ E →
      (∀ v ∈ sites siteID owner c, (state v).ScalarBound Z) →
      (∀ v ∈ sites siteID owner c, (state v).RowBound H) →
      (∀ v, (state v).TableBound T) → (∀ v, (state v).SplitFields (4*(M+E+1)^3) high) →
      ∀ bundles : List Bundle, (bundles.map (fun x => count x.factors)).sum + bundles.length ≤ 2*(M+1) →
      suppliedSize N cell c + gadgets*digits + (bundles.map Bundle.useBits).sum ≤ E →
      (∀ x ∈ bundles, count x.factors ≤ x.header.cap ∧ x.header.copies ≤ 4*(M+E+1)^3 ∧
        x.header.boxBase+x.header.orig+x.header.cap ≤ 4*(M+E+1)^3) →
      let start := countBase N cell state c + gadgets*digits
      let input := withWiring (cellInput N cell siteID edgeID portID owner state c gadgets digits external)
        (supplements start bundles)
      let words := CompactFrame.pack w (Packet.input input.directory input.privateWires input.external)
      words.length ≤ width order (1/2) ∧ cellClock w input ≤ order^25 ∧
        ∑ o ∈ choices cellDriver order words, o.2.value = input.weight := by
  obtain ⟨ω,hω,hw⟩ := eventually_cell_with_wiring T H B j R k hH
  refine ⟨ω,hω,?_⟩
  filter_upwards [hw] with order bound
  intro r M E w Z high hr hrω hM hE hw hwn hhigh hz D s m p P inst bits N cell siteID edgeID portID owner state
    c gadgets digits external howner hin hschema hpub hexp hg hd hdigits hext hscalar hrows htables hfactors
    bundles hsum htail hboxes
  let start := countBase N cell state c + gadgets*digits
  have checks := supplement_resources N state cell hin hexp bundles hsum htail hboxes
  apply bound r M E w Z high hr hrω hM hE hw hwn hhigh hz N cell siteID edgeID portID owner state
    c gadgets digits external howner hin hschema hpub hexp hg hd hdigits hext hscalar hrows htables hfactors
    (supplements start bundles)
  · exact checks.1
  · exact checks.2.1
  · exact checks.2.2

end Packing.Inherited.FinalCell

end BorderVNP
end Computability
end OAI
