import OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputs
import OAI.Computability.BorderVNP.RoutingISACellControlMemory
import OAI.Computability.BorderVNP.PackedBundleDirectoryRun

/-! # Recovering the scanner input from the actual grouped directory and owned-row producers -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports.ReportDirectory

open RoutingISA Packing.BundleDirectory DiagonalTallyAllocation
open TypedTaskBuilder

variable (d : Packing.BundleDirectory.Layout) (rows : CellControlRows.Layout) (l : ReportLayout)
    (owner : Fin d.bundles → Fin d.cells) (source : Fin d.bundles → ReportBundle)

/-- The marker-free public directory physically produced by stable grouping. -/
def grouped (m : ℕ → ℕ) :=
  d.image (groups owner fun j => (source j).header) m d.cells

/-- True private-assignment and receiving-bank bases are the same operands consumed
by the six-word native row producer, with the original sites in stable source order. -/
def directoryCell (mem : ℕ → ℕ) (counts : ℕ → Fin l.gadgets → Fin l.countWidth → Bool) (c : ℕ) : ReportCell l :=
  ⟨c,mem (rows.banks+2*c+1),mem (rows.offsets+2*rows.cables+c),mem (rows.live+2*rows.ports+c),
    «prefix» (groups owner fun j => (source j).header) c,(sourceRows owner c).map source,counts c⟩

/-- Compact traversal in the exact owned ordinal order published to frame slot 90. -/
noncomputable def directoryCells (mem : ℕ → ℕ) (counts : ℕ → Fin l.gadgets → Fin l.countWidth → Bool) :=
  List.ofFn fun i : Fin (rows.before mem rows.cells) =>
    directoryCell d rows l owner source mem counts (globalCell rows.toLayout mem i.val)

private theorem sixRows {α : Type*} (mem : ℕ → ℕ) (field : α → List ℕ) (fixed : ∀ a, (field a).length=6)
    (xs : List α) (base : ℕ) (atRow : ∀ i : Fin xs.length, CellPacket.WordsAt mem (base+6*i.val) (field xs[i.val])) :
    CellPacket.WordsAt mem base (xs.flatMap field) := by
  induction xs generalizing base with
  | nil => intro i; exact i.elim0
  | cons x xs ih =>
    have hx : CellPacket.WordsAt mem base (field x) := by simpa using atRow ⟨0,by simp⟩
    have tail := ih (base+6) (fun i => by
      have hh := atRow ⟨i.val+1,by simp⟩
      simpa [Nat.mul_add,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh)
    simp only [List.flatMap_cons]
    intro i
    by_cases before : i.val < (field x).length
    · rw [List.getElem_append_left before]
      exact hx ⟨i.val,before⟩
    · rw [List.getElem_append_right (Nat.le_of_not_gt before)]
      have hi := i.isLt
      simp only [List.length_append] at hi
      let j : Fin (xs.flatMap field).length := ⟨i.val-(field x).length,by omega⟩
      have addr : base+i.val=base+6+j.val := by dsimp [j]; have := fixed x; omega
      rw [addr]
      exact tail j

/-- The ABI and both independently produced tables use the allocated addresses. -/
structure Bindings (pre : BeforeTasks) (d : Packing.BundleDirectory.Layout) (rows : CellControlRows.Layout)
    (l : ReportLayout) : Prop where
  cells : rows.cells=d.cells
  cellLimit : d.cells ≤ pre.bound.cells
  bundleLimit : d.bundles ≤ pre.bound.bundles
  ranges : d.ranges=pre.ranges
  output : d.output=pre.bundleTable
  scannerRanges : rows.ranges=d.ranges
  frame : rows.frame=l.frame
  four : rows.four=pre.four
  six : rows.six=pre.six

private theorem published_read (r : CellControlRows.Layout) (m : ℕ → ℕ) (a : ℕ)
    (h : ¬r.outputs a) : r.published m a=m a := by
  have ne : a≠r.frame+90 := fun he => h (.inr (.inr he))
  rw [CellControlRows.Layout.published,Function.update_of_ne ne,CellControlRows.image_outside _ _ le_rfl h]

private theorem imageRows {pre : BeforeTasks} (bind : Bindings pre d rows l) {w : ℕ} (room : rows.Room w)
    (m : ℕ → ℕ) (counts : ℕ → Fin l.gadgets → Fin l.countWidth → Bool) (head : l.headers=pre.six) :
    let mem := grouped d owner source m
    CellPacket.WordsAt (rows.published mem) l.headers ((directoryCells d rows l owner source mem counts).flatMap
      ReportCell.headerWords) := by
  intro mem
  apply sixRows _ _ (fun _ => rfl)
  intro j
  have hj : j.val < rows.before mem rows.cells := by simpa [directoryCells] using j.isLt
  let n := globalCell rows.toLayout mem j.val
  have hn : n < d.cells := bind.cells ▸ (global_spec rows.toLayout mem hj).1
  let g := groups owner fun i => (source i).header
  have sep : apart d.ranges (2*d.cells) d.output (6*d.bundles) := Or.inl (by
    rw [bind.ranges,bind.output,BeforeTasks.bundleTable]; have := bind.cellLimit; omega)
  have ⟨range,_⟩ := d.image_cell g m (prefix_groups ..) sep d.cells le_rfl n hn
  have first : mem (d.ranges+2*n)=«prefix» g n := by simpa [mem,grouped,g] using range ⟨0,by simp⟩
  have past : mem (d.ranges+2*n+1)=«prefix» g (n+1) := by simpa [mem,grouped,g] using range ⟨1,by simp⟩
  have header := (CellControlRows.published_rows rows mem room hj).1
  change CellPacket.WordsAt (rows.published mem) (rows.six+6*j.val) (rows.rowSix mem n) at header
  rw [bind.six,←head] at header
  simp only [directoryCells,List.getElem_ofFn]
  change CellPacket.WordsAt (rows.published mem) (l.headers+6*j.val) (directoryCell d rows l owner source mem counts n).headerWords
  simpa only [CellControlRows.Layout.rowSix,bind.scannerRanges,first,past,prefix_succ,g,groups,
    List.length_map,ReportCell.headerWords,directoryCell] using header

private theorem data_banks {pre : BeforeTasks} (bind : Bindings pre d rows l) :
    rows.four+4*rows.cells ≤ d.output ∧ rows.six+6*rows.cells ≤ d.output ∧
      pre.start ≤ rows.four ∧ pre.start ≤ rows.six ∧ pre.start ≤ d.ranges ∧ pre.start ≤ d.output := by
  have n := bind.cellLimit
  simp only [bind.four,bind.six,bind.cells,bind.output,bind.ranges,BeforeTasks.bundleTable,BeforeTasks.ranges,
    BeforeTasks.six,BeforeTasks.four,BeforeTasks.merged,BeforeTasks.counters,BeforeTasks.supplement,BeforeTasks.tailWidths]
  omega

/-- The original physical input obtained by composing the two directory producers. -/
structure InputData {l : ReportLayout} (cs : List (ReportCell l)) (w description bundleLimit : ℕ)
    (m : ℕ → ℕ) : Prop where
  controls : l.ScannerControls m
  headers : CellPacket.WordsAt m l.headers (cs.flatMap ReportCell.headerWords)
  received : ∀ c ∈ cs, c.Received w description m
  ranges : ∀ c ∈ cs, c.first+c.bundles.length ≤ bundleLimit

/-- The chronological pre-task scanner inputs follow from the actual marker-free sort output,
independent owned-row publisher, and the one-copy private strings in the incoming banks.
The two producers can execute before the scanner without invalidating the opaque payload. -/
theorem physicalInput_owned {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout} {q : ReportCursor}
    (bind : Bindings pre d rows l) (w description : ℕ) (m : ℕ → ℕ) (counts : ℕ → Fin l.gadgets → Fin l.countWidth → Bool)
    (rowRoom : rows.Room w) (ctl : l.ScannerControls m) (controlBefore : l.control+28 ≤ banks.bankStart)
    (ctlFrame : l.control+28 ≤ l.frame ∨ l.frame+96 ≤ l.control)
    (receipt : ∀ j, (∃ c∈directoryCells d rows l owner source (grouped d owner source m) counts, (owner j).val=c.number) →
      (source j).delivered l description m ∧ (source j).SiteRoom l w description) :
    let mem := grouped d owner source m
    let cs := directoryCells d rows l owner source mem counts
    ReportAllocation pre post banks l cs q → SiteIntervals cs description banks.stride →
      InputData cs w description pre.bound.bundles (rows.published mem) := by
  intro mem cs alloc slots
  let g := groups owner fun j => (source j).header
  have cuts := data_banks d rows l bind
  have before := alloc.bankBefore
  have frame := alloc.frameBefore
  have unchanged (a : ℕ) (lo : a<pre.start) (ne : a≠l.frame+90) : rows.published mem a=m a := by
    rw [published_read _ _ _ (by simp only [CellControlRows.Layout.outputs,bind.frame]; omega)]
    exact d.image_outside g m d.cells a (.inl (by omega)) (.inl (by omega))
  have cword (j : ℕ) (hj : j<28) := unchanged (l.control+j) (by omega) (by omega)
  have controls : l.ScannerControls (rows.published mem) :=
    ⟨(cword 12 (by decide)).trans ctl.supplement,(cword 13 (by decide)).trans ctl.stride,
      (cword 14 (by decide)).trans ctl.counters,(cword 7 (by decide)).trans ctl.widths⟩
  have canonical (c : ReportCell l) (hc : c∈cs) :
      c=directoryCell d rows l owner source mem counts c.number ∧ c.number<d.cells := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    exact ⟨rfl,bind.cells ▸ (global_spec rows.toLayout mem i.isLt).1⟩
  refine ⟨controls,imageRows d rows l owner source bind rowRoom m counts alloc.headers,?_,?_⟩
  · intro c hc
    obtain ⟨real,hn⟩ := canonical c hc
    have first : c.first=«prefix» g c.number := congrArg ReportCell.first real
    have bundles : c.bundles=(sourceRows owner c.number).map source := congrArg ReportCell.bundles real
    have sep : apart d.ranges (2*d.cells) d.output (6*d.bundles) := Or.inl (by
      rw [bind.ranges,bind.output,BeforeTasks.bundleTable]; have := bind.cellLimit; omega)
    obtain ⟨_,row⟩ := d.image_cell g m (prefix_groups ..) sep d.cells le_rfl c.number hn
    constructor
    · rw [first,bundles,alloc.table,←bind.output]
      have same : ((sourceRows owner c.number).map source).flatMap (fun b => b.header.words)=cellWords g c.number := by
        simp [cellWords,g,groups,List.flatMap_map]
      rw [same]
      intro j
      rw [published_read _ _ _ (by
        have fr := rowRoom.outputApart.2.1
        simp only [CellControlRows.Layout.outputs]; omega)]
      exact row j
    · intro b hb
      have bounds := slots c hc b hb
      have cb := (alloc.receiving c hc).1
      have num : c.number < banks.cells := alloc.bankNumber c hc
      have stop := Nat.mul_le_mul_right banks.stride num
      rw [Nat.succ_mul] at stop
      rw [bundles,List.mem_map] at hb
      obtain ⟨i,hit,rfl⟩ := hb
      obtain ⟨raw,fit⟩ := receipt i ⟨c,hc,mem_sourceRows.mp hit⟩
      refine ⟨?_,fit⟩
      intro j
      rw [unchanged _ ?_ ?_]
      · exact raw j
      all_goals simp only [cb,CellBanks.Layout.bank] at bounds
      all_goals have := j.isLt
      all_goals omega
  · intro c hc
    obtain ⟨real,hn⟩ := canonical c hc
    have first : c.first=«prefix» g c.number := congrArg ReportCell.first real
    have bundles : c.bundles=(sourceRows owner c.number).map source := congrArg ReportCell.bundles real
    rw [first,bundles,List.length_map]
    have len : (sourceRows owner c.number).length=(g c.number).length := by simp [g,groups]
    rw [len,←prefix_succ]
    exact (prefix_mono g hn).trans ((prefix_groups ..).le.trans bind.bundleLimit)

/-- The same report inputs are available when all original bundle words are resident. -/
theorem physicalInput {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout} {q : ReportCursor}
    (bind : Bindings pre d rows l) (w description : ℕ) (m : ℕ → ℕ) (counts : ℕ → Fin l.gadgets → Fin l.countWidth → Bool)
    (rowRoom : rows.Room w) (ctl : l.ScannerControls m) (controlBefore : l.control+28 ≤ banks.bankStart)
    (ctlFrame : l.control+28 ≤ l.frame ∨ l.frame+96 ≤ l.control)
    (receipt : ∀ j, (source j).delivered l description m ∧ (source j).SiteRoom l w description) :
    let mem := grouped d owner source m
    let cs := directoryCells d rows l owner source mem counts
    ReportAllocation pre post banks l cs q → SiteIntervals cs description banks.stride →
      InputData cs w description pre.bound.bundles (rows.published mem) :=
  physicalInput_owned d rows l owner source bind w description m counts rowRoom ctl controlBefore ctlFrame (fun j _ => receipt j)

/-- The chronological pre-task scanner inputs follow from the actual marker-free sort output,
independent owned-row publisher, and the one-copy private strings in the incoming banks.
The two producers can execute before the scanner without invalidating the opaque payload. -/
theorem cellInputs {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout} {q : ReportCursor}
    (bind : Bindings pre d rows l) (w description : ℕ) (m : ℕ → ℕ) (counts : ℕ → Fin l.gadgets → Fin l.countWidth → Bool)
    (rowRoom : rows.Room w) (ctl : l.ScannerControls m) (controlBefore : l.control+28 ≤ banks.bankStart)
    (ctlFrame : l.control+28 ≤ l.frame ∨ l.frame+96 ≤ l.control)
    (receipt : ∀ j, (source j).delivered l description m ∧ (source j).SiteRoom l w description)
    (width : l.fieldWidth ≤ w) (coords : l.parameters+l.gadgets < 2^w) (space : post.fresh < 2^w) :
    let mem := grouped d owner source m
    let cs := directoryCells d rows l owner source mem counts
    ReportAllocation pre post banks l cs q → SiteIntervals cs description banks.stride →
      (∀ c ∈ cs, c.privateWires+c.supplied+c.tailWidth < 2^w) →
      DiagonalTallyCellReports.cellInputs w description cs q l.headers (rows.published mem) := by
  intro mem cs alloc slots privateEnd
  have data := physicalInput d rows l owner source bind w description m counts rowRoom ctl controlBefore
    ctlFrame receipt alloc slots
  exact alloc.cellInputs w description (rows.published mem) data.controls data.headers data.received
    slots controlBefore data.ranges privateEnd width coords space

end DiagonalTallyCellReports.ReportDirectory

end BorderVNP
end Computability
end OAI
