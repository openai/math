import OAI.Computability.BorderVNP.DiagonalReceivedReportExtent
import OAI.Computability.BorderVNP.DiagonalSchedulePrivateBudget

/-! # Original unsigned cell reports on the selected true native schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing Packing.CellAddresses Packing.BottomReports Packing.Inherited
open Site.Programs CellSparse DiagonalTallyCellReports TeamScales RoutingISA RoutingISA.TypedBatch
open scoped Classical

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

/-- Every guarded original route has passing private reports at exactly its
receiving sites. The ordinary cell allowance comes from the same physical
schedule as the sparse input driver, and covers every possible report tail. -/
theorem scheduled_guarded_reports {order r M E w Z high table rows B j coeff k : ℕ}
    (scheduled : Diagonal.PrivateCellBudgetAt 3076 table (B+10) (j+1) rows coeff k order r)
    (hn : 1 ≤ order) (hr : 1≤r) (enough : 9≤rows)
    (hM : M≤TeamScales.width order (1/5)) (hE : E≤TeamScales.width order (1/4))
    (hw : 0<w) (hwn : w≤order) (hhigh : high.size+1≤B*(logWidth r order+1)^j)
    (hz : 3*M+Z≤4*(M+E+1)^3) :
    ∀ {T C D ns ne np n d blocks b h K s : ℕ} {P J Team : Type} [Fintype P] [Fintype J]
        {bits : P → ℕ} {layout : Fin T → ReportLayout} (R : ReceivedRows layout C)
        (N : Network D P bits) (cell : N.Site → Fin C) (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
        (portID : P ↪ Fin np) (state : Site.Programs N) (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
        (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (ports : Ports bits) (owner : Fin ns → ℕ)
        (host : J ↪ N.Site) (bundle : J → Bundle) (origins : Fin C → List J),
      ReceivedBounds R N cell siteID owner state host bundle origins M E Z high table rows (coeff*(logWidth r order+1)^k) →
      ∀ (q : Routed (b:=b) (s:=s) owners) (raw : (c : Fin C) → Fin (externalBase N cell c (placedSize N state)) → Bool),
      GuardedCores N cell siteID edgeID portID state owners slot ports owner (R.countReports N cell state) q raw →
      ∀ u A, A ∈ R.assigned N cell siteID edgeID portID state owners slot ports owner (fun c => (origins c).map bundle)
        q raw u → A.Passing w order := by
  intro T C D ns ne np n d blocks b h K s P J Team instP instJ bits layout R N cell siteID edgeID portID state owners slot ports owner host bundle origins good q raw guard u A inList
  let bottom := fun c => (origins c).map bundle
  let key := fun v => (cell v).val
  let progs := fun v => (state v).program
  let row := R.assignedAt N cell siteID edgeID portID state owners slot ports owner bottom q raw
  change A ∈ List.ofFn (row u) at inList
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp inList
  let c := R.order ⟨u,i⟩
  let widths := FinalReports.bank_sizes N cell progs c
  let g := privateWires N cell (placedSize N state) c (raw c) ∘ Fin.cast widths.1
  let a := privateStaging N cell (placedSize N state) c (raw c) ∘ Fin.cast widths.2.1
  let x := pathSupply N cell edgeID portID owners slot ports q c ∘ Fin.cast widths.2.2
  have sg := sortedDirectory_signFree N key siteID edgeID portID owner progs c.val
    (countFields (FinalCell.countBase N key progs c.val) (layout u).gadgets (layout u).countWidth) good.unsigned
  have observed := R.assignedAt_observed N cell siteID edgeID portID state owners slot ports owner bottom q raw u i (guard.2 c)
  have pre : CellAddresses.bank N key c.val (fun v => (progs v).size) g a x = (row u i).pre := by
    change List.ofFn g ++ (List.ofFn a ++ List.ofFn x)=List.ofFn (Fin.append g a)++List.ofFn x
    rw [List.ofFn_fin_append,List.append_assoc]
  let bs := (origins c).map bundle
  let report := (R.cells u).get i
  let start := FinalCell.countBase N key progs c.val+(layout u).gadgets*(layout u).countWidth
  let reps := countFields (FinalCell.countBase N key progs c.val) (layout u).gadgets (layout u).countWidth
  let reg := CellAddresses.bank N key c.val (fun v => (progs v).size) g a x
  have seen := pre.symm ▸ observed
  have targets := FinalCell.retained_use_cores N key siteID edgeID portID owner good.ownerID progs c.val reps reg
    (origins c) host bundle (fun j => (good.retained j).2.choose) (good.belongs c)
    (fun j _ => (good.retained j).2.choose_spec.1) (fun j _ => (good.retained j).2.choose_spec.2)
    (fun j _ => (good.retained j).1) (by simp [reg,CellAddresses.bank]) seen
  obtain ⟨sum,tail,boxes⟩ := retained_call_bounds N key progs siteID host bundle good.retained c.val M E
    (layout u).gadgets (layout u).countWidth (origins c) (good.unique c) (good.belongs c) (good.copies c)
    good.incoming (good.publicLoad c) (good.expandedLoad c) (good.space u)
  have sizes := FinalCell.supplement_resources N progs key good.incoming (good.expandedLoad c) bs sum tail boxes
  apply FinalCell.assigned_passing N key c.val siteID edgeID portID owner progs report g a x bs (row u i).observations
    w order M hw good.ownerID good.incoming good.schema good.locality good.relative sg seen (good.ids u i)
    (good.expandedLoad c) (good.digitFit u) targets (good.uses u i)
  intro proposed
  let ext := List.ofFn x ++ List.ofFn proposed
  have length : ext.length ≤ E := by
    rw [show ext.length = suppliedSize N key c.val+report.tailWidth by simp [ext,key]]
    simpa only [ReportCell.tailWidth,report,good.uses u i,Nat.add_assoc] using tail
  let task := FinalCell.withWiring (FinalCell.cellInput N key siteID edgeID portID owner progs c.val (layout u).gadgets
    (layout u).countWidth ext) (supplements start bs)
  have cert := FinalCell.wiring_clock_format hn hr enough hM hE hhigh hz N key siteID edgeID portID owner progs
    c.val (layout u).gadgets (layout u).countWidth ext good.ownerID good.incoming good.schema
    (good.publicLoad c) (good.expandedLoad c) (good.gadgetCount u) (good.countWidth u) (good.widthBound u)
    (fun v _ => good.scalars v) (fun v _ => good.rowSize v) good.tableSize good.split (supplements start bs)
    sizes.1 sizes.2.1 sizes.2.2
  exact (scheduled M E w _ hM hE hw hwn task length cert.static cert.compact cert.records cert.reports
    cert.mass cert.raw cert.rawDigits cert.format cert.tables cert.digits cert.widths).2.1

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
