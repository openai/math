import OAI.Computability.BorderVNP.DiagonalNativeReportBindingReadback
import OAI.Computability.BorderVNP.DiagonalNativeSparseValues
import OAI.Computability.BorderVNP.FragmentRowsSparseLaunch
import OAI.Computability.BorderVNP.RoutingISAScheduleClockMergeSource
import OAI.Computability.BorderVNP.RoutingISAScheduleClockReportWords

/-! # Identifying the signed report recovered by the native sparse packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator DiagonalTallyAllocation CellSparse CellSparse.Packet
open private record_append from OAI.Computability.BorderVNP.CellDirectoryWire

/-- Decode an arbitrary actual sparse-report return at its native ordinal.
Both the counters and the raw digits refer to this very returning state. -/
theorem returned_report_binding {w description : ℕ} {l : ReportLayout}
    {cs : List (ReportCell l)} {q : ReportCursor} {pub : Arg → Word w} {m : Memory w}
    {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}
    (alloc : ReportAllocation pre post banks l cs q) (seed : PreparedReportInput pub m cs q description)
    {mac : TeamOpcode.Macros w 8} {s : Bank w} (r : Returns prepareCellReports pub mac s m) :
    let rows := ((assignedReportReturnEquiv seed mac s).symm r).val
    ∀ i : Fin rows.length, rows[i.val].BindingReadback
      ((rows.take i.val).foldl (fun a c => c.after a) q) (readings r.val.2.2) := by
  intro rows i
  have actual := assignedReportReturn_bindingReadback alloc seed mac s ((assignedReportReturnEquiv seed mac s).symm r) i
  rwa [Equiv.apply_symm_apply] at actual

/-- On a shared returned report RAM, the sparse cell's entire physical
suffix is the sampled count and use string, including unused zero digits. -/
theorem ReportCell.BindingReadback.sparseTail {w : ℕ} {mem : Memory w} {l : ReportLayout}
    {report : ReportCell l} {cursor : ReportCursor}
    (readback : report.BindingReadback cursor (readings mem))
    {a : SignedTaskArena.Layout} {f : FragmentRows.Layout} {data : ℕ → ℕ → Bool} {i : ℕ}
    (c : FragmentRows.SparseCell a f mem data i) (global : c.number.val=report.number)
    (tailBase : a.before.tailWidths=l.tailWidths)
    (bank : readings mem (f.host.cells+2*c.number.val+1)=report.external)
    (supply : readings mem (f.supplied+c.number.val)=report.supplied) : c.tail=report.bits := by
  have len := c.tailLength
  rw [tailBase,global,readback.width] at len
  have same : c.tail.length=report.bits.length := len.symm.trans report.bits_length.symm
  apply List.ext_getElem same
  intro j hj hj'
  have observed := readback.bits ⟨j,by simpa using hj'⟩
  have physical := c.reports j hj
  rw [bank,supply] at physical
  rw [List.getElem_map] at observed
  have flags : c.tail[j].toNat=report.bits[j].toNat := physical.symm.trans observed
  cases h : c.tail[j] <;> cases h' : report.bits[j] <;> simp_all

/-- Recover the binding rows from the native supplement source and its two
published counters. The decoder uses only the builder's input memory. -/
def readBindingRows (mem : ℕ → ℕ) (supp ctr : ℕ) : List Record :=
  let fields := List.ofFn (fun j : Fin (mem (ctr+1)) => mem (supp+j.val))
  ((list readRecord (mem ctr :: fields)).map Prod.fst).getD []

/-- Read the actual source record sequence before the task builder splices
it onto a private directory. No prior decoded record sequence is required. -/
theorem ReportCell.SupplementStored.readBindingRows {l : ReportLayout} {c : ReportCell l}
    {q : ReportCursor} {mem : ℕ → ℕ} (stored : c.SupplementStored q mem) :
    readBindingRows mem (l.supplement+c.number*l.supplementStride) (l.counters+2*c.number) =
      bindingRows c.bundles (c.localStart q) := by
  let rs := bindingRows c.bundles (c.localStart q)
  obtain ⟨resident,recordCount,wordCount⟩ := stored
  have fields : List.ofFn (fun j : Fin (mem (l.counters+2*c.number+1)) =>
      mem (l.supplement+c.number*l.supplementStride+j.val)) = rs.flatMap record := by
    apply List.ext_getElem (by simpa only [List.length_ofFn] using wordCount)
    intro j hj hr
    rw [List.getElem_ofFn]
    exact resident ⟨j,hr⟩
  have parsed : list readRecord (rs.length :: rs.flatMap record) = some (rs,[]) := by
    simpa only [fieldList,List.append_nil] using list_append record readRecord record_append rs []
  change DiagonalTallyCellReports.readBindingRows _ _ _=rs
  unfold DiagonalTallyCellReports.readBindingRows
  rw [fields,recordCount]
  change ((list readRecord (rs.length :: rs.flatMap record)).map Prod.fst).getD [] = rs
  rw [parsed]
  rfl

/-- Uniqueness of the variable-length record sequence in the real typed
packet. Actual record and word counts are separate native address fields. -/
private theorem records_eq {xs ys : List Record} (count : xs.length=ys.length)
    (body : xs.flatMap record=ys.flatMap record) : xs=ys := by
  let d (rows : List Record) : Directory := ⟨[],rows,[]⟩
  have equal : words (d xs) 0=words (d ys) 0 := by simp [words,d,fieldList,count,body]
  have decoded := congrArg parse equal
  rw [parse_words,parse_words] at decoded
  exact congrArg (fun p : ℕ × Directory => p.2.records) (Option.some.inj decoded)

/-- The supplement retained through the true argument-building prefix
contains exactly the ordered bindings written by the chosen report. -/
theorem ReportCell.SupplementStored.mergeRows {w table controls i : ℕ} {Slot : Type}
    {o : CellPacket.Supplement.Batch.Owned Slot} {m : Memory w}
    {l : ReportLayout} {c : ReportCell l} {q : ReportCursor}
    (saved : c.SupplementStored q (readings m))
    (merge : Evaluator.ScheduleClock.MergeFields o table controls i m)
    (counter : o.layout.counters=l.counters+2*c.number)
    (source : o.layout.supplement=l.supplement+c.number*l.supplementStride) :
    o.extra=bindingRows c.bundles (c.localStart q) := by
  obtain ⟨bits,rc,wc⟩ := saved
  have count := merge.privateCount
  have len := merge.privateWords
  rw [counter,rc] at count
  rw [counter,wc] at len
  apply records_eq count.symm
  apply List.ext_getElem len.symm
  intro j hj hj'
  have first := merge.original.supp ⟨j,hj⟩
  rw [source] at first
  exact first.symm.trans (bits ⟨j,hj'⟩)

end DiagonalTallyCellReports

namespace Diagonal.ExternalSew.Fragments

open VPVNP.BurstRAM Crossing Packing Packing.Directory Packing.CellAddresses Packing.Inherited
open RoutingISA RoutingISA.SparseExterior RoutingISA.CompactMachine Cube.Physical CellSparse
open DiagonalTallyCellReports
open scoped Classical

variable {D R r literalWidth link V g m n entries desc w : ℕ}
variable (arena : SignedTaskArena.Layout) (N : Network D (FreeBlock R V) (fun _ => g))
variable (cell : N.Site → Fin arena.fragments.cells) (edgeID : N.Edge ↪ Fin m) (portID : FreeBlock R V ↪ Fin n)
variable (head base : ℕ) (old returned : Memory w)
local notation "f" => FragmentRows.Layout.fromFrame head (readings returned)
variable (fits : (FragmentRows.Layout.fromFrame head (readings returned)).Fits w (readings returned))
variable (cells : arena.fragments.cells=(FragmentRows.Layout.fromFrame head (readings returned)).cells)
variable (rows : CableRows N cell edgeID portID (FragmentRows.Layout.fromFrame head (readings returned)).host (readings returned))
variable (hg : 0<g) (room : r*(2*literalWidth+R*link) ≤ V*g) (pp lp : ℕ → ℕ × ℕ)
variable (place : LivePlacement N cell edgeID portID lp)
local notation "supplied" => (fun c : ℕ => (readings returned) (FragmentRows.Layout.supplied f+c))
variable (counts : ∀ c, (readings returned) ((FragmentRows.Layout.fromFrame head (readings returned)).supplied+c.val)=suppliedSize N cell c)
variable (privateAfter : ∀ j : Fin entries, (readings returned) ((FragmentRows.Layout.fromFrame head (readings returned)).supplied+(pp j.val).1) ≤ (pp j.val).2)
variable (input : FreePort R r literalWidth → Bool) (ends : Bool → LiveBit N cell → Bool)
local notation "bank" => fillFree hg room input (fun _ => false)
local notation "data" => endData N cell edgeID portID bank ends
local notation "dir" => freeDirectory R r literalWidth link V g entries desc
local notation "published" => readings (Directory.ISA.publish old head base (Packing.Directory.Layout.directory dir pp lp))

include rows place counts privateAfter in
/-- The compact source attached to an actual native cell restores its routed
bank followed by exactly the bits selected by the physical report scan. -/
theorem owned_report_values {ordinal : ℕ} (c : FragmentRows.SparseCell arena f returned data ordinal)
    {l : ReportLayout} (report : ReportCell l) (cursor : ReportCursor)
    (readback : report.BindingReadback cursor (readings returned))
    (global : c.number.val=report.number) (tailBase : arena.before.tailWidths=l.tailWidths)
    (external : (readings returned) ((f).host.cells+2*c.number.val+1)=report.external)
    (width : (readings returned) ((f).supplied+c.number.val)=report.supplied)
    (original : readings old (head+8)=base) (apart : head+9 < base)
    (rowRoom : ((dir).directory pp lp).length < 2^w)
    (words : ∀ i : Fin ((dir).directory pp lp).length, ∀ x ∈ ((dir).directory pp lp)[i.val].words, x<2^w)
    (ptr : (readings returned) (head+8)=published (head+8)) (num : (readings returned) (head+9)=published (head+9))
    (kept : ∀ addr, base ≤ addr → addr < base+7*((dir).directory pp lp).length → (readings returned) addr=published addr) :
    (c.owned (fit:=fits) (cells:=cells)).field.values =
      List.ofFn (Placement.endSupply N cell c.number edgeID portID bank ends) ++ report.bits := by
  have actual := emitted_owned_values (entries:=entries) (desc:=desc) arena N cell edgeID portID head base old (readings returned)
    fits cells rows hg room pp lp place counts privateAfter input ends c.number
    ((readings returned) ((f).host.cells+2*c.number.val+1)) c.tail original apart rowRoom words ptr num kept c.ordered
  exact actual.trans (congrArg (List.append _) (readback.sparseTail c global tailBase external width))

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
