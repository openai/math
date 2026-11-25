import OAI.Computability.BorderVNP.PackedFinalAssignedReport
import OAI.Computability.BorderVNP.PackedBottomRetainedBudget

/-! # Authentic private report fibers for all sufficiently large orders -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalCell

open Filter Crossing Shortening CellSparse CellAddresses TeamScales BottomReports DiagonalTallyCellReports
open scoped Classical
open private load from OAI.Computability.BorderVNP.PackedBankCellStatic

set_option maxHeartbeats 2200000
set_option maxRecDepth 18000

/-- A native report row uses the actual marked positions of the same original
bundles. Arbitrary choices of their use bits preserve this length. -/
theorem physical_use_counts {J : Type*} (origins : List J) (bundle : J → Bundle) (body : J → List Factor)
    (bank : J → ℕ → Bool) (tape : ℕ → Bool) (offset : ℕ) :
    ((tapeBundles tape offset (origins.map fun j => physicalBundle (bundle j).header (body j)
      (bundle j).factors (bank j))).map ReportBundle.useCount).sum =
    ((origins.map bundle).map Bundle.useBits).sum := by
  simp only [tapeBundles_useCount,List.map_map,Function.comp_def,physicalBundle,ReportBundle.useCount,
    positions_length,Bundle.useBits]

/-- For each large order the true sparse evaluator has sufficient time on
every candidate report spelling. A successful original tagged assignment
therefore determines a passing native report fiber on the full actual cell. -/
theorem eventually_retained_passing (T H B j R k : ℕ) (hH : 9 ≤ H) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ᶠ order : ℕ in atTop, ∀ r M E w Z high : ℕ,
      1 ≤ r → (r:ℝ) ≤ 2^((order:ℝ)^ω) → M ≤ width order (1/5) → E ≤ width order (1/4) →
      0 < w → w ≤ order → high.size+1 ≤ B*(logWidth r order+1)^j → 3*M+Z ≤ 4*(M+E+1)^3 →
      ∀ {D s m p : ℕ} {P J : Type} [Fintype P] [Fintype J] {bits : P → ℕ}
        (N : Network D P bits) (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m)
        (portID : P ↪ Fin p) (owner : Fin s → ℕ) (state : N.Site → Site) (c : ℕ) {l : ReportLayout}
        (report : ReportCell l) (host : J ↪ N.Site) (bundle : J → Bundle) (origins : List J),
      (∀ v, owner (siteID v) = cell v) → (∀ v, (state v).incoming = incoming N v) →
      (∀ v, (state v).Schema) → (∀ v, (state v).Local) → (∀ v, (state v).RelativeBoxes) →
      load N cell state c false ≤ M → load N cell state c true ≤ M →
      l.gadgets ≤ M+1 → l.countWidth ≤ M+1 → l.countWidth ≤ R*(logWidth r order+1)^k →
      M < 2^l.countWidth → 3*M+l.gadgets*l.countWidth ≤ E →
      (∀ v ∈ sites siteID owner c, (state v).ScalarBound Z) →
      (∀ v ∈ sites siteID owner c, (state v).RowBound H) →
      (∀ v, (state v).TableBound T) → (∀ v, (state v).SplitFields (4*(M+E+1)^3) high) →
      (∀ v ∈ sites siteID owner c, ∀ fs ∈ (state v).boxes, ∀ f ∈ fs, f.IDRange l.gadgets) →
      RetainedBirths N cell state siteID host bundle → origins.Nodup →
      (∀ j ∈ origins, cell (host j)=c) →
      (∀ j ∈ origins, 0<(bundle j).header.copies ∧ 0<(bundle j).header.stride) →
      (report.bundles.map ReportBundle.useCount).sum=((origins.map bundle).map Bundle.useBits).sum →
      ∀ (g : Fin (guessedSize N cell c) → Bool) (a : Fin (siteSize N cell c (fun v => (state v).size)) → Bool)
        (x : Fin (suppliedSize N cell c) → Bool) (obs : List (Bool × Option ℕ)),
      let reps := countFields (countBase N cell state c) l.gadgets l.countWidth
      let init := directory owner N cell siteID edgeID portID state c reps
      let pre := CellAddresses.bank N cell c (fun v => (state v).size) g a x
      init.SignFree → init.guardedObservations (lookup pre)=some obs →
      (assignedReport N cell c siteID edgeID portID owner state report g a x (origins.map bundle) obs).Passing w order := by
  obtain ⟨ω,hω,hw⟩ := eventually_supplemented_cell T H B j R k hH
  refine ⟨ω,hω,?_⟩
  filter_upwards [hw] with order bound
  intro r M E w Z high hr hrω hM hE hw hwn hhigh hz D s m p P J instP instJ bits
    N cell siteID edgeID portID owner state c l report host bundle origins aligned incoming schema localSite relative
    hp he hg hd hdigits fits room scalar rows tables factors ids inventory nodup belongs positive counts
    g a x obs reps init pre unsigned seen
  let birth (j : J) := (inventory j).2.choose
  have cores := retained_use_cores N cell siteID edgeID portID owner aligned state c reps pre origins host bundle birth
    belongs (fun j _ => (inventory j).2.choose_spec.1) (fun j _ => (inventory j).2.choose_spec.2)
    (fun j _ => (inventory j).1) (by simp [pre,CellAddresses.bank]) seen
  obtain ⟨hrows,htail,hbundles⟩ := retained_call_bounds N cell state siteID host bundle inventory c M E
    l.gadgets l.countWidth origins nodup belongs positive incoming hp he room
  apply assigned_passing N cell c siteID edgeID portID owner state report g a x (origins.map bundle) obs
    w order M hw aligned incoming schema localSite relative unsigned seen ids he fits cores counts
  intro z
  have length : (List.ofFn x ++ List.ofFn z).length ≤ E := by
    rw [List.length_append,List.length_ofFn,List.length_ofFn]
    simpa only [ReportCell.tailWidth,counts,Nat.add_assoc] using htail
  exact (bound r M E w Z high hr hrω hM hE hw hwn hhigh hz N cell siteID edgeID portID owner state c
    l.gadgets l.countWidth _ aligned incoming schema hp he hg hd hdigits length scalar rows tables factors
    (origins.map bundle) hrows htail hbundles).2.1

end Packing.Inherited.FinalCell

end BorderVNP
end Computability
end OAI
