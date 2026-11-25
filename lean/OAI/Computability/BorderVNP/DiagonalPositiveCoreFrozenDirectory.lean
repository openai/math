import OAI.Computability.BorderVNP.DiagonalPositiveCoreDirectories
import OAI.Computability.BorderVNP.RoutingISASignedPrepSourceRows

/-! # Comparing the actual grouped report directories across proposed claims -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports.ReportDirectory

open RoutingISA TypedTaskBuilder Evaluator.SignedPrep Packing.BundleDirectory
open scoped Classical

/-- The geometry retained by each one-copy site. Only its expanded uses are
assigned after the report directory is built. -/
structure SameBundleSource (a b : ReportBundle) : Prop where
  header : a.header=b.header
  factors : a.factors=b.factors
  positions : a.positions=b.positions

/-- Readable immutable columns at each global cell, allowing distinct physical
memories and row control layouts. -/
structure SameCellColumns (a b : CellControlRows.Layout) (m n : ℕ → ℕ) : Prop where
  count : a.cells=b.cells
  owned : ∀ c<a.cells, a.owner m c=a.team ↔ b.owner n c=b.team
  bank : ∀ c<a.cells, m (a.banks+2*c+1)=n (b.banks+2*c+1)
  supplied : ∀ c<a.cells, m (a.offsets+2*a.cables+c)=n (b.offsets+2*b.cables+c)
  privateWires : ∀ c<a.cells, m (a.live+2*a.ports+c)=n (b.live+2*b.ports+c)

private def frozenBundle (b : ReportBundle) := b.withTape (fun _ => false) 0

private def frozenCell {l : ReportLayout} (c : ReportCell l) : ReportCell l :=
  {c with counts := fun _ _ => false, bundles := c.bundles.map frozenBundle}

private theorem freeze_bundles (bs : List ReportBundle) (p : ℕ) :
    tapeBundles (fun _ => false) p bs=bs.map frozenBundle := by
  induction bs generalizing p with
  | nil => rfl
  | cons b bs ih => simp only [tapeBundles,List.map_cons,ih]; rfl

private theorem freeze_cells {l : ReportLayout} (cs : List (ReportCell l)) (p : ℕ) :
    tapeCells (fun _ => false) p cs=cs.map frozenCell := by
  induction cs generalizing p with
  | nil => rfl
  | cons c cs ih => simp only [tapeCells,List.map_cons,ReportCell.withTape,freeze_bundles,ih]; rfl

private theorem frozen_source {a b : ReportBundle} (eq : SameBundleSource a b) : frozenBundle a=frozenBundle b := by
  obtain ⟨h,fs,ps,us⟩ := a
  obtain ⟨k,gs,qs,vs⟩ := b
  obtain ⟨rfl,rfl,rfl⟩ := eq
  rfl

private theorem frozen_groups {A B C E : ℕ} (h : Fin A → Fin C) (k : Fin B → Fin E)
    (f : Fin A → ReportBundle) (g : Fin B → ReportBundle) (size : A=B)
    (home : ∀ j, (h j).val=(k (Fin.cast size j)).val)
    (rows : ∀ j, SameBundleSource (f j) (g (Fin.cast size j))) :
    (groups h (fun j => (f j).header))=groups k (fun j => (g j).header) ∧
    ∀ c, ((sourceRows h c).map f).map frozenBundle=((sourceRows k c).map g).map frozenBundle := by
  subst B
  have indices (c : ℕ) : sourceRows h c=sourceRows k c := by simp only [sourceRows,home,Fin.cast_refl,id_eq]
  have head (j : Fin A) : (f j).header=(g j).header := (rows j).header
  have source (j : Fin A) : frozenBundle (f j)=frozenBundle (g j) := frozen_source (rows j)
  constructor
  · funext c
    simp only [groups,indices,head]
  · intro c
    simp only [indices,List.map_map,Function.comp_def,source]

private theorem SameCellColumns.before {a b : CellControlRows.Layout} {m n : ℕ → ℕ} (cols : SameCellColumns a b m n)
    (c : ℕ) (bound : c≤a.cells) : a.before m c=b.before n c := by
  induction c with
  | zero => rfl
  | succ c ih =>
    simp only [TypedTaskBuilder.Layout.before,ih (by omega),cols.owned c (by omega)]

private theorem SameCellColumns.global {a b : CellControlRows.Layout} {m n : ℕ → ℕ} (cols : SameCellColumns a b m n)
    (i : ℕ) (valid : i<a.before m a.cells) : globalCell a.toLayout m i=globalCell b.toLayout n i := by
  let c := globalCell a.toLayout m i
  obtain ⟨inside,owned,ordinal⟩ := global_spec a.toLayout m valid
  have native := global_at b.toLayout n (c:=c) (inside.trans_eq cols.count) ((cols.owned c inside).mp owned)
  rw [← cols.before c inside.le,ordinal] at native
  exact native.symm

/-- The actual owner scan and stable bundle grouping on any two physical memories
give the same report inputs after clearing the sampled digits and uses. The first
bundle offset is derived from the stable grouping, independently of the guesses. -/
theorem directoryCells_same_reports {l k : ReportLayout} (d e : Packing.BundleDirectory.Layout)
    (a b : CellControlRows.Layout) (host : Fin d.bundles → Fin d.cells) (host' : Fin e.bundles → Fin e.cells)
    (f : Fin d.bundles → ReportBundle) (g : Fin e.bundles → ReportBundle) (m n : ℕ → ℕ)
    (x : ℕ → Fin l.gadgets → Fin l.countWidth → Bool) (y : ℕ → Fin k.gadgets → Fin k.countWidth → Bool)
    (layout : l=k) (cols : SameCellColumns a b m n) (size : d.bundles=e.bundles)
    (home : ∀ j,(host j).val=(host' (Fin.cast size j)).val)
    (source : ∀ j,SameBundleSource (f j) (g (Fin.cast size j))) :
    SameReportCells (directoryCells d a l host f m x) (directoryCells e b k host' g n y) := by
  subst k
  obtain ⟨groupsEq,bs⟩ := frozen_groups host host' f g size home source
  have length : a.before m a.cells=b.before n b.cells := (cols.before _ le_rfl).trans (congrArg (b.before n) cols.count)
  refine ⟨rfl,?_⟩
  change eraseReportBits _=eraseReportBits _
  simp only [eraseReportBits,freeze_cells,directoryCells,List.map_ofFn,Function.comp_def]
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using length
  · intro i hi hj
    have bound : i<a.before m a.cells := by simpa only [List.length_ofFn] using hi
    let c := globalCell a.toLayout m i
    have fit : c<a.cells := (global_spec a.toLayout m bound).1
    simp only [List.getElem_ofFn,← cols.global i bound]
    change frozenCell (directoryCell d a l host f m x c)=frozenCell (directoryCell e b l host' g n y c)
    simp only [directoryCell,frozenCell,cols.bank c fit,cols.supplied c fit,cols.privateWires c fit,groupsEq,bs]

end DiagonalTallyCellReports.ReportDirectory

end BorderVNP
end Computability
end OAI
