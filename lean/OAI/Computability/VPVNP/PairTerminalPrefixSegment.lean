import OAI.Computability.VPVNP.CompressorSliceAdjacency
import OAI.Computability.VPVNP.PairTerminalPrefixWorker
import OAI.Computability.VPVNP.LiveHeaderUnique
import OAI.Computability.VPVNP.CompressorSourceTransport

/-!
# Execution of the live terminal-prefix pass

The width and start pointers and the arc count are reloaded from the terminal
header on each reset-entry call. The scan leaves them intact. When the cursor
reaches the stored count, the closing call writes the descriptor displacement
plus the accumulated bit width to the role-offset cell.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalPrefix.Segment

open BurstRAM BurstRAM.PrivateRAM CompressorRecords Compression
open scoped Fin.CommRing

variable {w a g : ℕ}

/-- The header words used by the prefix stage fit in memory. The two arc arrays
are disjoint from these header words. -/
structure HeaderLayout (pub : Fin 11 → Word w) (T : IncidenceDirectory w)
    (base : Word w) (n : ℕ) : Prop where
  fits : (Worker.header pub).val + 15 ≤ 2 ^ w
  startsApart : base.val + n ≤ (Worker.header pub).val ∨ (Worker.header pub).val + 15 ≤ base.val
  widthsApart : T.width.val + n ≤ (Worker.header pub).val ∨
    (Worker.header pub).val + 15 ≤ T.width.val

private theorem header_addr {h : Word w} {j : ℕ} (fit : h.val + 15 ≤ 2 ^ w) (hj : j < 15) :
    (h + (j : Word w)).val = h.val + j := by
  rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : j < 2 ^ w),
    Nat.mod_eq_of_lt (by omega)]

/-- The active width and start intervals and the live header words used by this
stage. This set bounds all external probes before any disjointness condition
on the controller's own cells is imposed. -/
def probeRegion (pub : Fin 11 → Word w) (T : IncidenceDirectory w) (base : Word w)
    (n x : ℕ) : Prop :=
  ((Worker.header pub).val + 5 ≤ x ∧ x < (Worker.header pub).val + 15) ∨
  (T.width.val ≤ x ∧ x < T.width.val + n) ∨ (base.val ≤ x ∧ x < base.val + n)

/-- Read and write addresses of a report are both in the stage's data region. -/
def footprint (pub : Fin 11 → Word w) (T : IncidenceDirectory w) (base : Word w)
    (n : ℕ) (r : Report w) : Prop :=
  SourceTransport.Reads (probeRegion pub T base n) r.events ∧
    SourceTransport.Writes (probeRegion pub T base n) r.events

open private pre read from OAI.Computability.VPVNP.PairTerminalPrefixWorker

private theorem read_eq (m : Memory w) (a : Word w) :
    (read m a : Event w) = .read a (m a.val) := rfl

private theorem active_footprint {pub : Fin 11 → Word w} {T : IncidenceDirectory w} {base : Word w}
    {n : ℕ} (layout : HeaderLayout pub T base n)
    (regions : SliceRAM.PrefixRegions (operands T base (Worker.header pub + 12)) n)
    {i : Word w} (hi : i.val < n) (m : Memory w)
    (widthHead : m (Worker.header pub + 9).val = T.width)
    (startHead : m (Worker.header pub + 11).val = base) :
    footprint pub T base n (Worker.activeReport pub i m) := by
  have header (j : ℕ) (hlo : 5 ≤ j) (hhi : j < 15) :
      probeRegion pub T base n (Worker.header pub + (j : Word w)).val := by
    left
    rw [header_addr layout.fits hhi]
    omega
  have widths : probeRegion pub T base n (T.width + i).val := by
    right; left
    have hfit : T.width.val + n ≤ 2 ^ w := regions.widthsFit
    rw [Fin.val_add, Nat.mod_eq_of_lt (by omega)]
    omega
  have starts : probeRegion pub T base n (base + i).val := by
    right; right
    have hfit : base.val + n ≤ 2 ^ w := regions.startsFit
    rw [Fin.val_add, Nat.mod_eq_of_lt (by omega)]
    omega
  constructor <;> intro a v mem
  · simp only [Worker.activeReport, pre, read_eq, List.mem_append, List.mem_replicate,
      List.mem_cons, List.not_mem_nil, Event.read.injEq, reduceCtorEq, and_false, false_or,
      or_false] at mem
    rcases mem with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact header 8 (by decide) (by decide)
    · exact header 9 (by decide) (by decide)
    · rwa [widthHead]
    · exact header 11 (by decide) (by decide)
    · exact header 12 (by decide) (by decide)
  · simp only [Worker.activeReport, pre, read_eq, List.mem_append, List.mem_replicate,
      List.mem_cons, List.not_mem_nil, Event.write.injEq, reduceCtorEq, and_false, false_or,
      or_false] at mem
    rcases mem with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · rwa [startHead]
    · exact header 12 (by decide) (by decide)

private theorem close_footprint {pub : Fin 11 → Word w} {T : IncidenceDirectory w} {base : Word w}
    {n : ℕ} (layout : HeaderLayout pub T base n) (i : Word w) (m : Memory w) :
    footprint pub T base n (Worker.closeReport pub i m) := by
  have header (j : ℕ) (hlo : 5 ≤ j) (hhi : j < 15) :
      probeRegion pub T base n (Worker.header pub + (j : Word w)).val := by
    left
    rw [header_addr layout.fits hhi]
    omega
  constructor <;> intro a v mem
  · simp only [Worker.closeReport, pre, read_eq, List.mem_append, List.mem_replicate,
      List.mem_cons, List.not_mem_nil, Event.read.injEq, reduceCtorEq, and_false, false_or,
      or_false] at mem
    rcases mem with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact header 8 (by decide) (by decide)
    · exact header 5 (by decide) (by decide)
    · exact header 12 (by decide) (by decide)
  · simp only [Worker.closeReport, pre, read_eq, List.mem_append, List.mem_replicate,
      List.mem_cons, List.not_mem_nil, Event.write.injEq, reduceCtorEq, and_false, false_or,
      or_false] at mem
    obtain ⟨rfl, _⟩ := mem
    exact header 14 (by decide) (by decide)

open private prefixAt_step from OAI.Computability.VPVNP.CompressorSlicePrefix

private theorem header_read {pub : Fin 11 → Word w} {T : IncidenceDirectory w} {base : Word w}
    {ws : List ℕ} (layout : HeaderLayout pub T base ws.length) {k : ℕ} (hk : k ≤ ws.length)
    {initial m : Memory w}
    (h : SliceRAM.PrefixAt (operands T base (Worker.header pub + 12)) ws initial m k)
    (j : ℕ) (hj : j < 15) (hn : j ≠ 12) :
    m (Worker.header pub + (j : Word w)).val = initial (Worker.header pub + (j : Word w)).val := by
  apply h.outside
  · change _ ≠ (Worker.header pub + 12).val
    have ht : (Worker.header pub + 12).val = (Worker.header pub).val + 12 := by
      simpa only [Nat.cast_ofNat] using header_addr (j := 12) layout.fits (by decide)
    rw [header_addr layout.fits hj, ht]
    omega
  · change _ < base.val ∨ base.val + k ≤ _
    rw [header_addr layout.fits hj]
    have := layout.startsApart
    omega

/-- Run any remaining portion of the active scan. Its memory invariant is the
one for the three-operand width scan, although the eleven-operand table obtains
the pointer values through external probes on every call. -/
private theorem active_from (pub : Fin 11 → Word w) (T : IncidenceDirectory w) (base : Word w)
    (ws : List ℕ) (initial : Memory w) (layout : HeaderLayout pub T base ws.length)
    (regions : SliceRAM.PrefixRegions (operands T base (Worker.header pub + 12)) ws.length)
    (countFit : ws.length < 2 ^ w) (sumFit : ws.sum < 2 ^ w)
    (count : initial (Worker.header pub + 8).val = (ws.length : Word w))
    (widthHead : initial (Worker.header pub + 9).val = T.width)
    (startHead : initial (Worker.header pub + 11).val = base)
    {k : ℕ} {m : Memory w}
    (progress : SliceRAM.PrefixAt (operands T base (Worker.header pub + 12)) ws initial m k)
    (steps : ℕ) (bound : k + steps ≤ ws.length) :
    let P := (Worker.table.instantiate w pub).program
    ∃ rs, runSegment P 30 (some (k : Word w)) m (List.replicate steps []) = some rs ∧
      SliceRAM.PrefixAt (operands T base (Worker.header pub + 12)) ws initial
        (after m (eventLog rs)) (k + steps) ∧
      endState (some (k : Word w)) rs = some ((k + steps : ℕ) : Word w) ∧
      rs.length = steps ∧ ∀ r ∈ rs, (r.probes = 7 ∧ r.events.length = 29) ∧
        footprint pub T base ws.length r := by
  dsimp only
  induction steps generalizing k m with
  | zero => exact ⟨[], rfl, progress, rfl, rfl, by simp⟩
  | succ steps ih =>
    have same := header_read layout (k := k) (by omega) progress
    have hd : Worker.data pub m = operands T base (Worker.header pub + 12) := by
      funext j
      fin_cases j
      · exact (same 9 (by decide) (by decide)).trans widthHead
      · exact (same 11 (by decide) (by decide)).trans startHead
      · rfl
    have hcount : m (Worker.header pub + 8).val = (ws.length : Word w) :=
      (same 8 (by decide) (by decide)).trans count
    have hval : (k : Word w).val = k := Nat.mod_eq_of_lt (by omega)
    have active : (k : Word w) ≠ m (Worker.header pub + 8).val := by
      rw [hcount]
      intro he
      have := congrArg Fin.val he
      rw [hval, Fin.val_natCast, Nat.mod_eq_of_lt countFit] at this
      omega
    let rep := Worker.activeReport pub (k : Word w) m
    have stepped := prefixAt_step regions sumFit (i := (k : Word w)) (by omega) (hval ▸ progress)
    rw [hval, ← hd, ← Worker.active_image] at stepped
    have next : SliceRAM.PrefixAt (operands T base (Worker.header pub + 12)) ws initial
        (after m rep.events) (k + 1) := by rwa [hd] at stepped
    obtain ⟨rs, run, filled, ended, calls, cost⟩ := ih next (by omega)
    refine ⟨rep :: rs, ?_, ?_, ?_, by simp [calls], ?_⟩
    · rw [List.replicate_succ, runSegment, Worker.active pub _ m active]
      simp only [Worker.active_result, ← Nat.cast_one (R := Word w), ← Nat.cast_add]
      rw [show runSegment (Worker.table.instantiate w pub).program 30 (some ((k + 1 : ℕ) : Word w))
        (after m rep.events) (List.replicate steps []) = some rs from run]
      rfl
    · rw [show after m (eventLog (rep :: rs)) = after (after m rep.events) (eventLog rs)
          from List.foldl_append, show k + (steps + 1) = k + 1 + steps by omega]
      exact filled
    · change endState (some ((k : Word w) + 1)) rs = _
      simpa only [Nat.cast_add, Nat.cast_one, show k + (steps + 1) = k + 1 + steps by omega]
        using ended
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · refine ⟨Worker.active_cost .., active_footprint layout regions (by omega) m ?_ ?_⟩
        · exact (same 9 (by decide) (by decide)).trans widthHead
        · exact (same 11 (by decide) (by decide)).trans startHead
      · exact cost r hr

open private width_cells take_sum from OAI.Computability.VPVNP.PairTerminalPrefix

/-- The native scan returns the arc count as its persistent state. Its last
accumulator and its stored starts have their exact natural-number values. -/
theorem run_active (pub : Fin 11 → Word w) (X : State a g) (T : IncidenceDirectory w)
    (base : Word w) (m : Memory w) (rep : T.ActualColumns X m)
    (layout : HeaderLayout pub T base (arcCount X))
    (regions : SliceRAM.PrefixRegions (operands T base (Worker.header pub + 12)) (arcCount X))
    (countFit : arcCount X < 2 ^ w) (totalFit : X.totalWidth < 2 ^ w)
    (count : m (Worker.header pub + 8).val = (arcCount X : Word w))
    (widthHead : m (Worker.header pub + 9).val = T.width)
    (startHead : m (Worker.header pub + 11).val = base)
    (zero : m (Worker.header pub + 12).val = 0) :
    let P := (Worker.table.instantiate w pub).program
    ∃ rs, runSegment P 30 (some 0) m (List.replicate (arcCount X) []) = some rs ∧
      Stored X T base (Worker.header pub + 12) m (after m (eventLog rs)) ∧
      endState (some 0) rs = some (arcCount X : Word w) ∧ rs.length = arcCount X ∧
      ∀ r ∈ rs, (r.probes = 7 ∧ r.events.length = 29) ∧ footprint pub T base (arcCount X) r := by
  let ws := List.ofFn (width X)
  let h := Worker.header pub
  have hlen : ws.length = arcCount X := List.length_ofFn
  have hsum : ws.sum = X.totalWidth := List.sum_ofFn.trans (width_sum X)
  have init : SliceRAM.PrefixAt (operands T base (h + 12)) ws m m 0 := by
    refine ⟨?_, fun _ h => by omega, ?_, fun _ _ _ => rfl⟩
    · intro i hi
      change (m (T.width.val + i)).val = ws[i]
      simpa only [ws, List.getElem_ofFn] using
        width_cells X T m rep regions.widthsFit totalFit ⟨i, hlen ▸ hi⟩
    · change (m (h + 12).val).val = (ws.take 0).sum
      rw [zero]; rfl
  obtain ⟨rs, executed, filled, ended, calls, cost⟩ := active_from pub T base ws m
    (hlen ▸ layout) (hlen ▸ regions) (hlen.trans_lt countFit) (hsum.trans_lt totalFit)
    (hlen ▸ count) widthHead startHead init ws.length (by omega)
  simp only [Nat.cast_zero, Nat.zero_add, hlen] at executed ended calls cost
  refine ⟨rs, executed, ⟨?_, ?_, ?_, ?_⟩, ended, calls, cost⟩
  · intro i
    exact (filled.starts i.val (by simpa only [Nat.zero_add, hlen] using i.isLt)).trans
      (take_sum (width X) i)
  · change (after m (eventLog rs) (operands T base (Worker.header pub + 12) 2).val).val = _
    simpa only [Nat.zero_add, List.take_length, hsum] using filled.total
  · intro i
    change (after m (eventLog rs)
      ((operands T base (Worker.header pub + 12) 0).val + i.val)).val = _
    simpa only [ws, List.getElem_ofFn] using filled.widths i.val (i.isLt.trans_eq hlen.symm)
  · intro x hx hx'
    apply filled.outside x hx
    change x < base.val ∨ base.val + (0 + ws.length) ≤ x
    simpa only [Nat.zero_add, hlen] using hx'

/-- The role-tag displacement published by the closing call. -/
def roleValue (pub : Fin 11 → Word w) (X : State a g) (m : Memory w) : Word w :=
  m (Worker.header pub + 5).val + (X.totalWidth : Word w)

/-- Complete native execution, including the accepting call. The frame of the
stored prefix is relative to the initial memory with the role cell updated. -/
structure Run (pub : Fin 11 → Word w) (X : State a g) (T : IncidenceDirectory w)
    (base : Word w) (m : Memory w) (rs : List (Report w)) : Prop where
  native : runSegment (Worker.table.instantiate w pub).program 30 (some 0) m
    (List.replicate (arcCount X + 1) []) = some rs
  halt : endState (some 0) rs = none
  calls : rs.length = arcCount X + 1
  probes : (rs.map Report.probes).sum = 7 * arcCount X + 4
  instructions : (rs.map (fun r => r.events.length + 1)).sum = 30 * arcCount X + 24
  bounds : ∀ r ∈ rs, r.probes ≤ 7 ∧ r.events.length ≤ 29
  stored : Stored X T base (Worker.header pub + 12)
    (writeMemory m (Worker.header pub + 14) (roleValue pub X m)) (after m (eventLog rs))
  accesses : ∀ r ∈ rs, footprint pub T base (arcCount X) r
  role : after m (eventLog rs) (Worker.header pub + 14).val = roleValue pub X m

private theorem stored_header_read {pub : Fin 11 → Word w} {X : State a g}
    {T : IncidenceDirectory w} {base : Word w} {m ready : Memory w}
    (layout : HeaderLayout pub T base (arcCount X))
    (stored : Stored X T base (Worker.header pub + 12) m ready)
    (j : ℕ) (hj : j < 15) (hn : j ≠ 12) :
    ready (Worker.header pub + (j : Word w)).val = m (Worker.header pub + (j : Word w)).val := by
  have ht : (Worker.header pub + 12).val = (Worker.header pub).val + 12 := by
    simpa only [Nat.cast_ofNat] using header_addr (j := 12) layout.fits (by decide)
  apply stored.outside
  · rw [header_addr layout.fits hj, ht]
    omega
  · rw [header_addr layout.fits hj]
    have := layout.startsApart
    omega

private theorem store_role {pub : Fin 11 → Word w} {X : State a g}
    {T : IncidenceDirectory w} {base : Word w} {m ready : Memory w}
    (layout : HeaderLayout pub T base (arcCount X))
    (stored : Stored X T base (Worker.header pub + 12) m ready) (v : Word w) :
    Stored X T base (Worker.header pub + 12) (writeMemory m (Worker.header pub + 14) v)
      (writeMemory ready (Worker.header pub + 14) v) := by
  let h := Worker.header pub
  have ht : (h + 12).val = h.val + 12 := by
    simpa only [Nat.cast_ofNat] using header_addr (j := 12) layout.fits (by decide)
  have hr : (h + 14).val = h.val + 14 := by
    simpa only [Nat.cast_ofNat] using header_addr (j := 14) layout.fits (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    have := layout.startsApart
    have hi := i.isLt
    have hx : base.val + i.val ≠ (h + 14).val := by dsimp only [h] at hr ⊢; omega
    dsimp only [h] at hx
    simpa only [writeMemory, ite_eq_right hx] using stored.start i
  · have hx : (h + 12).val ≠ (h + 14).val := by omega
    dsimp only [h] at hx
    simpa only [writeMemory, ite_eq_right hx] using stored.total
  · intro i
    have := layout.widthsApart
    have hi := i.isLt
    have hx : T.width.val + i.val ≠ (h + 14).val := by dsimp only [h] at hr ⊢; omega
    dsimp only [h] at hx
    simpa only [writeMemory, ite_eq_right hx] using stored.widths i
  · intro x htotal hstart
    simp only [writeMemory, stored.outside x htotal hstart]

open private sum_constant_cost from OAI.Computability.VPVNP.CompressorSlicePreparation

/-- All active arc visits and the accepting role-offset publication form a
single reset-entry run, including for a final network with no arcs. -/
theorem run (pub : Fin 11 → Word w) (X : State a g) (T : IncidenceDirectory w)
    (base : Word w) (m : Memory w) (rep : T.ActualColumns X m)
    (layout : HeaderLayout pub T base (arcCount X))
    (regions : SliceRAM.PrefixRegions (operands T base (Worker.header pub + 12)) (arcCount X))
    (countFit : arcCount X < 2 ^ w) (totalFit : X.totalWidth < 2 ^ w)
    (count : m (Worker.header pub + 8).val = (arcCount X : Word w))
    (widthHead : m (Worker.header pub + 9).val = T.width)
    (startHead : m (Worker.header pub + 11).val = base)
    (zero : m (Worker.header pub + 12).val = 0) :
    ∃ rs, Run pub X T base m rs := by
  obtain ⟨rs, native, stored, ended, calls, cost⟩ := run_active pub X T base m rep layout
    regions countFit totalFit count widthHead startHead zero
  let ready := after m (eventLog rs)
  let n := arcCount X
  let h := Worker.header pub
  let last := Worker.closeReport pub (n : Word w) ready
  have hcount : (n : Word w) = ready (h + 8).val := by
    have hc := stored_header_read layout stored 8 (by decide) (by decide)
    simpa only [Nat.cast_ofNat] using count.symm.trans hc.symm
  have close := Worker.close pub (n : Word w) ready hcount
  have total : ready (h + 12).val = (X.totalWidth : Word w) := by
    apply Fin.ext
    rw [Fin.val_natCast, Nat.mod_eq_of_lt totalFit]
    exact stored.total
  have hdesc : ready (h + 5).val = m (h + 5).val := by
    simpa only [Nat.cast_ofNat] using stored_header_read layout stored 5 (by decide) (by decide)
  have image : after m (eventLog (rs ++ [last])) =
      writeMemory ready (h + 14) (roleValue pub X m) := by
    have hm : after m (eventLog (rs ++ [last])) = after ready last.events := by
      simp only [eventLog, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, after, List.foldl_append, ready]
    rw [hm, Worker.close_image, roleValue, hdesc, total]
  have lastCost := Worker.close_cost pub (n : Word w) ready
  refine ⟨rs ++ [last], ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [List.replicate_succ', PrimedSchedule.runSegment_append, native]
    dsimp only [n, ready] at close
    simp only [Option.bind_some, ended, runSegment, close, Option.map_some]
    rfl
  · rw [endState_append]
    rfl
  · simp [calls]
  · simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero]
    rw [sum_constant_cost Report.probes rs 7 (fun r hr => (cost r hr).1.1), calls]
    exact congrArg _ lastCost.1
  · simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero]
    rw [sum_constant_cost (fun r : Report w => r.events.length + 1) rs 30
        (fun r hr => by rw [(cost r hr).1.2]), calls]
    rw [show last.events.length = 23 from lastCost.2]
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨hp, ht⟩ := (cost r hr).1
      exact ⟨hp.le, ht.le⟩
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨lastCost.1.le.trans (by decide), lastCost.2.le.trans (by decide)⟩
  · rw [image]
    exact store_role layout stored _
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact (cost r hr).2
    · obtain rfl := List.mem_singleton.mp hr
      exact close_footprint layout _ _
  · rw [image]
    simp only [writeMemory, h, ↓reduceIte]

/-- The terminating stage admits precisely its canonical sequence of empty
choice streams, with the same reports on every accepting execution. -/
theorem Run.unique {pub : Fin 11 → Word w} {X : State a g} {T : IncidenceDirectory w}
    {base : Word w} {m : Memory w} {rs ts : List (Report w)} (run : Run pub X T base m rs)
    {bits : List (List Bool)} (native : runSegment (Worker.table.instantiate w pub).program 30
      (some 0) m bits = some ts) (halt : endState (some 0) ts = none) :
    bits = List.replicate (arcCount X + 1) [] ∧ ts = rs :=
  accepted_empty_unique run.native run.halt native halt

/-- Total charged work counts one unit for starting each call in addition to
its external probes. -/
theorem Run.charge {pub : Fin 11 → Word w} {X : State a g} {T : IncidenceDirectory w}
    {base : Word w} {m : Memory w} {rs : List (Report w)} (run : Run pub X T base m rs) :
    RAMBuckets.cost Report.probes rs = 8 * arcCount X + 5 := by
  rw [SliceRAM.adjCost_eq_length_add_probes, run.calls, run.probes]
  omega

/-- Every read and write in the entire completed segment avoids the linked
controller's phase cell and saved-state cell. -/
theorem Run.controller_frame {pub : Fin 11 → Word w} {X : State a g} {T : IncidenceDirectory w}
    {base : Word w} {m : Memory w} {rs : List (Report w)} (run : Run pub X T base m rs)
    (fits : (Worker.header pub).val + 32 ≤ 2 ^ w)
    (widthsBelow : T.width.val + arcCount X ≤ (Worker.header pub).val)
    (startsBelow : base.val + arcCount X ≤ (Worker.header pub).val) :
    let away := fun x => x ≠ (Worker.header pub).val ∧ x ≠ (Worker.header pub + 31).val
    SourceTransport.Reads away (eventLog rs) ∧ SourceTransport.Writes away (eventLog rs) := by
  have small : 31 < 2 ^ w := by omega
  have saved : (Worker.header pub + 31).val = (Worker.header pub).val + 31 := by
    change ((Worker.header pub).val + (31 % 2 ^ w)) % (2 ^ w) = _
    rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt (by omega)]
  have safe (x : ℕ) (h : probeRegion pub T base (arcCount X) x) :
      x ≠ (Worker.header pub).val ∧ x ≠ (Worker.header pub + 31).val := by
    rw [saved]
    unfold probeRegion at h
    omega
  constructor <;> intro a v mem
  · obtain ⟨r, hr, he⟩ := List.mem_flatMap.mp mem
    exact safe _ ((run.accesses r hr).1 a v he)
  · obtain ⟨r, hr, he⟩ := List.mem_flatMap.mp mem
    exact safe _ ((run.accesses r hr).2 a v he)

/-- With room for the descriptor words and final bits together, the published
word is their ordinary natural-number sum. -/
theorem Run.role_val {pub : Fin 11 → Word w} {X : State a g} {T : IncidenceDirectory w}
    {base : Word w} {m : Memory w} {rs : List (Report w)} (run : Run pub X T base m rs)
    (fit : (m (Worker.header pub + 5).val).val + X.totalWidth < 2 ^ w) :
    (after m (eventLog rs) (Worker.header pub + 14).val).val =
      (m (Worker.header pub + 5).val).val + X.totalWidth := by
  rw [run.role, roleValue, Fin.val_add, Fin.val_natCast,
    Nat.mod_eq_of_lt (by omega : X.totalWidth < 2 ^ w), Nat.mod_eq_of_lt fit]

end PairSimulation.TerminalPrefix.Segment

end VPVNP
end Computability
end OAI
