import OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsDirectory
import OAI.Computability.BorderVNP.DiagonalTallyReportChoiceCover

/-! # The original received and allocated inputs support every possible report tape -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open DiagonalTallyAllocation RoutingISA

private theorem tape_map {l : ReportLayout} {α : Type*} (a : ℕ → Bool) (f : ReportCell l → α)
    (same : ∀ c j, f (c.withTape a j)=f c) (cs : List (ReportCell l)) (j : ℕ) :
    (tapeCells a j cs).map f=cs.map f := by
  induction cs generalizing j <;> simp [tapeCells, *]

private theorem from_cells {l : ReportLayout} (a : ℕ → Bool) (cs : List (ReportCell l)) (p : ℕ)
    {d : ReportCell l} (h : d ∈ tapeCells a p cs) : ∃ c∈cs, ∃ j, d=c.withTape a j := by
  induction cs generalizing p with
  | nil => simp [tapeCells] at h
  | cons c cs ih =>
    rcases List.mem_cons.mp h with rfl|h
    · exact ⟨c,List.mem_cons_self,p,rfl⟩
    · obtain ⟨b,hb,j,rfl⟩ := ih _ h
      exact ⟨b,.tail _ hb,j,rfl⟩

private theorem from_bundles (a : ℕ → Bool) (bs : List ReportBundle) (p : ℕ) {s : ReportBundle}
    (h : s ∈ tapeBundles a p bs) : ∃ b∈bs, ∃ j, s=b.withTape a j := by
  induction bs generalizing p with
  | nil => simp [tapeBundles] at h
  | cons b bs ih =>
    rcases List.mem_cons.mp h with rfl|h
    · exact ⟨b,List.mem_cons_self,p,rfl⟩
    · obtain ⟨d,hd,j,rfl⟩ := ih _ h
      exact ⟨d,.tail _ hd,j,rfl⟩

private theorem tape_supplement (a : ℕ → Bool) (bs : List ReportBundle) (p : ℕ) :
    supplementWords (tapeBundles a p bs)=supplementWords bs := by
  induction bs generalizing p with
  | nil => rfl
  | cons b bs ih =>
    simp only [tapeBundles,supplementWords,List.map_cons,List.sum_cons]
    exact congrArg (fun n => 9*b.positions.length+6+n) (ih _)

private theorem tape_headers (a : ℕ → Bool) (bs : List ReportBundle) (p : ℕ) :
    (tapeBundles a p bs).flatMap (fun b => b.header.words)=bs.flatMap (fun b => b.header.words) := by
  induction bs generalizing p <;> simp [tapeBundles,ReportBundle.withTape, *]

private theorem tape_Received {l : ReportLayout} {c : ReportCell l} {w description : ℕ} {m : ℕ → ℕ}
    (h : c.Received w description m) (a : ℕ → Bool) (p : ℕ) : (c.withTape a p).Received w description m := by
  refine ⟨?_,?_⟩
  · simpa only [ReportCell.withTape,tape_headers] using h.headers
  · intro b hb
    obtain ⟨d,hd,j,rfl⟩ := from_bundles a c.bundles _ hb
    obtain ⟨del,room⟩ := h.sites d hd
    exact ⟨del,⟨room.body,room.descriptionRoom,room.values,room.marked,room.padding,room.translated⟩⟩

variable {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}

/-- Replacing guessed bits changes none of the finite-index assignments, actual bank
volumes or original placement fields used by the physical allocation. -/
theorem ReportAllocation.tape (h : ReportAllocation pre post banks l cs q) (a : ℕ → Bool) (p : ℕ) :
    ReportAllocation pre post banks l (tapeCells a p cs) q := by
  refine ⟨h.bankCells,h.postCells,h.frameBefore,h.bankBefore,h.preBefore,h.headers,h.table,h.widths,
    h.supplement,h.stride,h.counters,h.gadgets,h.countWidth,h.initial,?_,?_,?_,?_,?_,?_⟩
  · obtain ⟨ix,number⟩ := h.owned
    let eqLen := tapeCells_length a p cs
    let ord := finCongr eqLen
    refine ⟨ord.toEmbedding.trans ix,?_⟩
    intro i
    have same := tape_map a ReportCell.number (fun _ _ => rfl) cs p
    have hn := congrArg (fun xs : List ℕ => xs[i.val]?) same
    have left : i.val < (tapeCells a p cs).length := i.isLt
    have right : i.val < cs.length := (ord i).isLt
    simp only [List.getElem?_map,List.getElem?_eq_getElem left,List.getElem?_eq_getElem right,
      Option.map_some,Option.some.injEq] at hn
    exact hn.trans (number (ord i))
  · intro d hd
    obtain ⟨c,hc,j,rfl⟩ := from_cells a cs p hd
    change c.external=banks.bank c.number ∧ c.supplied+(c.withTape a j).tailWidth ≤ banks.stride
    rw [ReportCell.withTape_tailWidth]
    exact h.receiving c hc
  · intro d hd
    obtain ⟨c,hc,j,rfl⟩ := from_cells a cs p hd
    simpa only [ReportCell.withTape,tape_supplement] using h.supplements c hc
  · rw [tape_map a _ (by intro c j; simp [ReportCell.withTape])]
    exact h.bundleCount
  · intro d hd b hb
    obtain ⟨c,hc,j,rfl⟩ := from_cells a cs p hd
    obtain ⟨s,hs,k,rfl⟩ := from_bundles a c.bundles _ hb
    exact h.marked c hc s hs
  · unfold teamWeighted
    rw [tape_map a _ (by intro c j; simp [ReportCell.withTape,weightedCopies])]
    exact h.uses

/-- The native traversal's original-memory precondition is valid for every report tape,
with precisely the same control words, private receipts and reserved capacities. -/
theorem ReportAllocation.cellInputs_tape (h : ReportAllocation pre post banks l cs q) (w description : ℕ)
    (m : ℕ → ℕ) (data : ReportDirectory.InputData cs w description pre.bound.bundles m)
    (site : SiteIntervals cs description banks.stride) (controlBefore : l.control+28 ≤ banks.bankStart)
    (privateEnd : ∀ c ∈ cs, c.privateWires+c.supplied+c.tailWidth<2^w)
    (width : l.fieldWidth ≤ w) (coords : l.parameters+l.gadgets<2^w) (room : post.fresh<2^w)
    (a : ℕ → Bool) (p : ℕ) : DiagonalTallyCellReports.cellInputs w description (tapeCells a p cs) q l.headers m := by
  refine (h.tape a p).cellInputs w description m data.controls ?_ ?_ ?_ controlBefore ?_ ?_ width coords room
  · have eqn := congrArg List.flatten (tape_map a ReportCell.headerWords (fun c j => c.withTape_headerWords a j) cs p)
    change (tapeCells a p cs).flatMap ReportCell.headerWords=cs.flatMap ReportCell.headerWords at eqn
    rw [eqn]
    exact data.headers
  · intro d hd
    obtain ⟨c,hc,j,rfl⟩ := from_cells a cs p hd
    exact tape_Received (data.received c hc) a j
  · intro d hd b hb
    obtain ⟨c,hc,j,rfl⟩ := from_cells a cs p hd
    obtain ⟨s,hs,k,rfl⟩ := from_bundles a c.bundles _ hb
    rw [ReportCell.withTape_tailWidth]
    exact site c hc s hs
  · intro d hd
    obtain ⟨c,hc,j,rfl⟩ := from_cells a cs p hd
    simpa only [ReportCell.withTape,tapeBundles_length] using data.ranges c hc
  · intro d hd
    obtain ⟨c,hc,j,rfl⟩ := from_cells a cs p hd
    rw [ReportCell.withTape_tailWidth]
    exact privateEnd c hc

namespace ReportDirectory

/-- Every choice tape is executable against the true published memory and the same
fixed allocation of the stable original bundle directory. -/
theorem cellInputs_tape (d : Packing.BundleDirectory.Layout) (rows : CellControlRows.Layout) (l : ReportLayout)
    (owner : Fin d.bundles → Fin d.cells) (source : Fin d.bundles → ReportBundle)
    {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout} {q : ReportCursor}
    (bind : Bindings pre d rows l) (w description : ℕ) (m : ℕ → ℕ) (counts : ℕ → Fin l.gadgets → Fin l.countWidth → Bool)
    (rowRoom : rows.Room w) (ctl : l.ScannerControls m) (controlBefore : l.control+28 ≤ banks.bankStart)
    (ctlFrame : l.control+28 ≤ l.frame ∨ l.frame+96 ≤ l.control)
    (receipt : ∀ j, (source j).delivered l description m ∧ (source j).SiteRoom l w description)
    (width : l.fieldWidth ≤ w) (coords : l.parameters+l.gadgets < 2^w) (space : post.fresh < 2^w) :
    let mem := grouped d owner source m
    let cs := directoryCells d rows l owner source mem counts
    ReportAllocation pre post banks l cs q → SiteIntervals cs description banks.stride →
      (∀ c ∈ cs, c.privateWires+c.supplied+c.tailWidth < 2^w) →
      ∀ a : ℕ → Bool, DiagonalTallyCellReports.cellInputs w description (tapeCells a 0 cs) q l.headers
        (rows.published mem) := by
  intro mem cs alloc slots privateEnd a
  have data := physicalInput d rows l owner source bind w description m counts rowRoom ctl controlBefore
    ctlFrame receipt alloc slots
  exact alloc.cellInputs_tape w description (rows.published mem) data slots controlBefore privateEnd width coords space a 0

end ReportDirectory

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
