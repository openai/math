import OAI.Computability.BorderVNP.PackedFinalCellFields
import OAI.Computability.BorderVNP.PackedSupplementResources
import OAI.Computability.BorderVNP.PackedFinalCellRowBounds
import OAI.Computability.BorderVNP.PackedFieldBoundSites
import OAI.Computability.BorderVNP.RoutingISATypedPrivateClock

/-! # Native signed execution on the actual owner-sorted geometry packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalCell

open Filter Crossing Shortening CellSparse CellAddresses InheritedBank TeamScales DiagonalTallyCellReports
open RoutingISA RoutingISA.CompactMachine RoutingISA.TypedBatch VPVNP.BurstRAM
open scoped Classical
open private load from OAI.Computability.BorderVNP.PackedBankCellStatic
open private compact_digits small_width from OAI.Computability.BorderVNP.RoutingISATypedPrivateClock

set_option maxHeartbeats 1800000
set_option maxRecDepth 18000

/-- True sparse private input at a final cell, with the original one-copy
tables and a fixed-width subtotal field for every gadget. -/
noncomputable def cellInput {D s m p : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m)
    (portID : P ↪ Fin p) (owner : Fin s → ℕ) (state : N.Site → Site) (c gadgets digits : ℕ)
    (external : List Bool) : CellInput :=
  ⟨directory owner N cell siteID edgeID portID state c (countFields (countBase N cell state c) gadgets digits),
   privateBits N cell state c, external⟩

/-- Additional source-weight equalities and padding tests follow the sorted
site records. Both input pieces share the same private and external bit bank. -/
def withWiring (input : CellInput) (extra : List Record) : CellInput :=
  {input with directory := BottomReports.appendRows input.directory extra}

/-- Format and resource bounds of the actual sorted directory, independent of the
physical representation chosen for the exterior bits. -/
structure ClockFormat (input : CellInput) (M E high order r T H B j R k : ℕ) : Prop where
  static : input.directory.StaticBounds 3076 M
  compact : input.directory.CompactFields input.privateWires (4*(M+E+1)^3)
  records : input.directory.records.length ≤ 4*(M+E+1)^3
  reports : input.directory.reportedCounts.length ≤ 4*(M+E+1)^3
  mass : Packet.storedMass input.directory ≤ 3076*(M+1)^2
  raw : Packet.RawFields input.directory input.privateWires (max (4*(M+E+1)^3) high)
  rawDigits : (max (4*(M+E+1)^3) high).size+1 ≤ (B+10)*(logWidth r order+1)^(j+1)
  format : ∀ rec ∈ input.directory.records, (Packet.record rec).length ≤ H
  tables : ∀ fs ∈ input.directory.boxes, ∀ f ∈ fs, f.TableBound T
  digits : ∀ bs ∈ input.directory.reportedCounts, bs.length ≤ R*(logWidth r order+1)^k
  widths : input.directory.ProfileWidths

/-- The real inherited sites and the appended source-weight tests meet the
private compiler's format and scalar-width bounds. -/
theorem wiring_clock_format {order r M E Z high T H B j R k : ℕ} (hn : 1 ≤ order) (hr : 1 ≤ r)
    (hH : 9 ≤ H) (hM : M ≤ width order (1/5)) (hE : E ≤ width order (1/4))
    (hhigh : high.size+1 ≤ B*(logWidth r order+1)^j) (hz : 3*M+Z ≤ 4*(M+E+1)^3)
    {D s m p : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m)
    (portID : P ↪ Fin p) (owner : Fin s → ℕ) (state : N.Site → Site) (c gadgets digits : ℕ) (external : List Bool)
    (howner : ∀ v, owner (siteID v) = cell v) (hin : ∀ v, (state v).incoming = incoming N v)
    (hschema : ∀ v, (state v).Schema) (hpub : load N cell state c false ≤ M) (hexp : load N cell state c true ≤ M)
    (hg : gadgets ≤ M+1) (hd : digits ≤ M+1) (hdigits : digits ≤ R*(logWidth r order+1)^k)
    (hscalar : ∀ v ∈ sites siteID owner c, (state v).ScalarBound Z)
    (hrows : ∀ v ∈ sites siteID owner c, (state v).RowBound H) (htables : ∀ v, (state v).TableBound T)
    (hfactors : ∀ v, (state v).SplitFields (4*(M+E+1)^3) high)
    (extra : List Record) (hlen : extra.length ≤ 2*(M+1))
    (hextra : ∀ rec ∈ extra, BottomReports.Wiring rec)
    (hfields : ∀ rec ∈ extra, Packet.RecordFields rec (4*(M+E+1)^3)) :
    ClockFormat (withWiring (cellInput N cell siteID edgeID portID owner state c gadgets digits external) extra)
      M E high order r T H B j R k := by
  let base := countBase N cell state c
  let rs := countFields base gadgets digits
  let initial := cellInput N cell siteID edgeID portID owner state c gadgets digits external
  let input := withWiring initial extra
  let V := 4*(M+E+1)^3
  let L := logWidth r order+1
  have hL : 1 ≤ L := Nat.succ_pos _
  have hV : V.size+1 ≤ 10*L := compact_digits hr (hM.trans (small_width hn _ (by norm_num)))
    (hE.trans (small_width hn _ (by norm_num)))
  have raw : (max V high).size+1 ≤ (B+10)*L^(j+1) := by
    rcases max_choice V high with hv|hh
    · rw [hv]
      have h1 : L ≤ L^(j+1) := Nat.le_self_pow (Nat.succ_ne_zero _) _
      exact hV.trans (Nat.mul_le_mul (by omega) h1)
    · rw [hh]
      exact hhigh.trans (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hL (Nat.le_succ _)))
  obtain ⟨static,store,_,reps,_⟩ := compiler_static N cell siteID edgeID portID owner state c base gadgets digits M E
    howner hschema hpub hexp hg hd
  obtain ⟨compact,fields⟩ := compiler_fields N cell siteID edgeID portID owner state c gadgets digits M E Z high
    howner hin hschema hpub hexp hg hd hz hscalar (fun v _ => hfactors v)
  have rows := record_count_le N cell siteID edgeID portID owner state c rs howner
  have rowCount : initial.directory.records.length + extra.length ≤ V := by
    have h₁ := rows.trans (Nat.mul_le_mul_left 2 hpub)
    have h₂ : M+1 ≤ (M+E+1)^3 := (show M+1 ≤ M+E+1 by omega).trans (Nat.le_self_pow (by decide) _)
    change (directory owner N cell siteID edgeID portID state c rs).records.length+extra.length ≤ 4*(M+E+1)^3
    omega
  have rowLength : input.directory.records.length ≤ V := by
    simpa only [input,withWiring,BottomReports.appendRows,List.length_append] using rowCount
  obtain ⟨localFields,rawFields⟩ := BottomReports.append_fields compact fields (le_max_left ..) extra hextra hfields
    (rowCount.trans (le_max_left ..))
  refine ⟨BottomReports.append_static static extra hextra hlen,localFields,rowLength,reps,
    store.trans (Nat.mul_le_mul_right _ (by decide)),rawFields,raw,?_,?_,?_,?_⟩
  · exact BottomReports.append_format hH (directory_rowBound owner N cell siteID edgeID portID state c rs hH hrows) extra hextra
  · exact sortedDirectory_tableBound N cell siteID edgeID portID owner state c rs htables
  · intro bs h
    rw [countField_length base gadgets digits h]
    exact hdigits
  · exact BottomReports.append_profile (directory_profileWidths owner N cell siteID edgeID portID state c rs
      (fun v _ => hschema v)) extra hextra

/-- The stretching exponent and order threshold precede every geometry,
program, external bit vector and local site. The fixed native call on that
actual sorted packet respects both paper limits and realizes its exact signed
cell contraction. -/
theorem eventually_cell_with_wiring (T H B j R k : ℕ) (hH : 9 ≤ H) :
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
      ∀ extra : List Record, extra.length ≤ 2*(M+1) →
      (∀ rec ∈ extra, BottomReports.Wiring rec) → (∀ rec ∈ extra, Packet.RecordFields rec (4*(M+E+1)^3)) →
      let input := withWiring (cellInput N cell siteID edgeID portID owner state c gadgets digits external) extra
      let words := CompactFrame.pack w (Packet.input input.directory input.privateWires input.external)
      words.length ≤ width order (1/2) ∧ cellClock w input ≤ order^25 ∧
        ∑ o ∈ choices cellDriver order words, o.2.value = input.weight := by
  obtain ⟨ω,hω,hw⟩ := eventually_private_cell 3076 T (B+10) (j+1) H R k
  refine ⟨ω,hω,?_⟩
  filter_upwards [hw,eventually_ge_atTop 1] with order hclock hn
  intro r M E w Z high hr hrω hM hE hw hwn hhigh hz D s m p P inst bits N cell siteID edgeID portID owner state
    c gadgets digits external howner hin hschema hpub hexp hg hd hdigits hext hscalar hrows htables hfactors extra hlen hextra hfields
  let input := withWiring (cellInput N cell siteID edgeID portID owner state c gadgets digits external) extra
  have format := wiring_clock_format hn hr hH hM hE hhigh hz N cell siteID edgeID portID owner state c gadgets
    digits external howner hin hschema hpub hexp hg hd hdigits hscalar hrows htables hfactors extra hlen hextra hfields
  exact hclock r M E w _ hr hrω hM hE hw hwn input hext format.static format.compact format.records format.reports
    format.mass format.raw format.rawDigits format.format format.tables format.digits format.widths

/-- Native signed evaluation on the sorted cell before optional source-weight checks. -/
theorem eventually_sorted_cell (T H B j R k : ℕ) (hH : 9 ≤ H) :
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
      let input := cellInput N cell siteID edgeID portID owner state c gadgets digits external
      let words := CompactFrame.pack w (Packet.input input.directory input.privateWires input.external)
      words.length ≤ width order (1/2) ∧ cellClock w input ≤ order^25 ∧
        ∑ o ∈ choices cellDriver order words, o.2.value = input.weight := by
  obtain ⟨ω,hω,hw⟩ := eventually_cell_with_wiring T H B j R k hH
  refine ⟨ω,hω,?_⟩
  filter_upwards [hw] with order h
  intro r M E w Z high hr hrω hM hE hw hwn hhigh hz D s m p P inst bits N cell siteID edgeID portID owner state
    c gadgets digits external howner hin hschema hpub hexp hg hd hdigits hext hscalar hrows htables hfactors
  have res := h r M E w Z high hr hrω hM hE hw hwn hhigh hz N cell siteID edgeID portID owner state
    c gadgets digits external howner hin hschema hpub hexp hg hd hdigits hext hscalar hrows htables hfactors
    [] (Nat.zero_le _) (by simp) (by simp)
  simpa only [withWiring,BottomReports.appendRows,List.append_nil] using res

end Packing.Inherited.FinalCell

end BorderVNP
end Computability
end OAI
