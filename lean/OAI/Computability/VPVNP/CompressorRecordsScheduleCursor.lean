import OAI.Computability.VPVNP.CompressorRecordsSchedule
import OAI.Computability.VPVNP.CompressorRecordsCursor

/-!
# Executing the cursor incidence scan in the descriptor dispatcher

Each row writes six entries. The external tag and twelve frame cells therefore
retain their values throughout the scan when they are disjoint from the six
output columns. At the exclusive bound the linked worker writes the controller
tag and returns the initial cursor for the controller.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Schedule

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- All row writes in the scanned interval avoid the dispatch tag and the
twelve input cells (bound and eleven public words). -/
def CursorDisjoint (ports : Ports w) (pub : Fin 11 → Word w) (k n : ℕ) : Prop :=
  ∀ j, k ≤ j → j < k + n → ∀ av ∈ CursorRAM.rowWrites pub j,
    av.1 ≠ ports.tag ∧ ∀ u : Fin 12, av.1 ≠ ports.activeFrame + (u.val : Word w)

private theorem fold_away (xs : List (Word w × Word w)) (m : Memory w) (addr : Word w)
    (h : ∀ av ∈ xs, av.1 ≠ addr) :
    xs.foldl (fun mem av ↦ writeMemory mem av.1 av.2) m addr.val = m addr.val := by
  induction xs generalizing m with
  | nil => rfl
  | cons av xs ih =>
    rw [List.foldl_cons, ih _ (fun a ha ↦ h a (List.mem_cons_of_mem _ ha))]
    exact ite_eq_right (fun he ↦ h av (List.mem_cons_self ..) (Fin.ext he.symm))

/-- A single visit leaves each protected address available to the next call,
regardless of earlier contents of the output columns. -/
theorem cursor_row_preserves (ports : Ports w) (pub : Fin 11 → Word w) (j : ℕ)
    (m : Memory w)
    (h : ∀ av ∈ CursorRAM.rowWrites pub j, av.1 ≠ ports.tag ∧
      ∀ u : Fin 12, av.1 ≠ ports.activeFrame + (u.val : Word w)) :
    let out := after m (CursorRAM.events pub (Fin.ofNat _ j))
    out ports.tag.val = m ports.tag.val ∧
    stopWord ports.activeFrame out = stopWord ports.activeFrame m ∧
    (parameters ports.activeFrame out : Fin 11 → Word w) = parameters ports.activeFrame m := by
  dsimp only
  rw [CursorRAM.events_after]
  have keep (addr : Word w) (h' : ∀ av ∈ CursorRAM.rowWrites pub j, av.1 ≠ addr) :=
    fold_away (CursorRAM.rowWrites pub j) m addr h'
  refine ⟨keep _ (fun av ha ↦ (h av ha).1), keep _ ?_, ?_⟩
  · intro av ha
    simpa using (h av ha).2 0
  · funext i
    exact keep _ (fun av ha ↦ (h av ha).2 i.succ)

/-- Every cursor returned by the body is the next row number. Together with
frame preservation this gives the dispatch guard at every call boundary. -/
theorem cursor_valid_trace (ports : Ports w) (pub : Fin 11 → Word w)
    (k n : ℕ) (m : Memory w) (bound : Word w)
    (hk : k+n = bound.val) (hready : Ready cursorRefresh 0 ports pub bound m)
    (hsep : CursorDisjoint ports pub k n) :
    ValidTrace cursorRefresh 0 ports pub bound (Fin.ofNat _ k) m (CursorRAM.scanReports pub k n) := by
  induction n generalizing k m with
  | zero =>
    have he : Fin.ofNat (2^w) k = bound := Fin.ext (by
      simp only [Nat.add_zero] at hk
      rw [Fin.val_ofNat, hk, Nat.mod_eq_of_lt bound.isLt])
    exact ⟨hready,he.ge⟩
  | succ n ih =>
    have hlt : k < bound.val := by omega
    have hstate : Fin.ofNat (2^w) k < bound := by
      change k % (2^w) < bound.val
      rwa [Nat.mod_eq_of_lt (hlt.trans bound.isLt)]
    obtain ⟨ht, hb, hp⟩ := cursor_row_preserves ports pub k m (hsep k le_rfl (by omega))
    refine ⟨hready,hstate,Fin.ofNat _ (k+1),rfl,ih (k+1) _ (by omega)
      ⟨ht.trans hready.1, hb.trans hready.2.1, hp.trans hready.2.2⟩ ?_⟩
    exact fun j hj h ↦ hsep j (by omega) (by omega)

/-- Chronological reports of all data calls and the final transfer. The
closing call reads the same frame and sends the next call to the controller. -/
def cursorPassReports (ports : Ports w) (pub : Fin 11 → Word w) (k n : ℕ)
    (m : Memory w) : List (Report w) :=
  let rs := CursorRAM.scanReports pub k n
  linkedRows cursorRefresh 0 ports m rs ++
    [closedLinkedReport cursorRefresh 0 ports (after m (eventLog rs))]

variable {p r : ℕ}

/-- Execute all rows from the current cursor through the exclusive bound
and resume the controller with the exact new incidence columns. -/
theorem cursor_segment (controller : Template p r 5) (ports : Ports w)
    (pub : Fin 11 → Word w) (k n : ℕ) (m : Memory w) (bound : Word w)
    (hk : k+n = bound.val) (hready : Ready cursorRefresh 0 ports pub bound m)
    (hsep : CursorDisjoint ports pub k n) (fits : 3 ≤ 2^w)
    {cap : ℕ} (hcap : 119 ≤ cap) (tail : List (List Bool)) :
    let D := (machine cursorRefresh controller ports).program
    let out := after m (eventLog (CursorRAM.scanReports pub k n))
    runSegment D cap (some (Fin.ofNat _ k)) m (List.replicate n [] ++ [] :: tail) =
      (runSegment D cap (some 0) (writeMemory out ports.tag 0) tail).map
        (fun more ↦ cursorPassReports ports pub k n m ++ more) := by
  have h := worker_segment cursorRefresh controller 0 ports pub bound (Fin.ofNat _ k) m
    (List.replicate n []) (CursorRAM.scanReports pub k n) (1+CursorRAM.visit.length) cap (by decide)
    fits hcap (CursorRAM.scan_native pub k n m) (cursor_valid_trace ports pub k n m bound hk hready hsep) tail
  simpa only [cursorPassReports, List.append_assoc, List.singleton_append] using h

private theorem linked_cursor_rows (ports : Ports w) (pub : Fin 11 → Word w) (k n : ℕ)
    (m : Memory w) :
    let source := CursorRAM.scanReports pub k n
    let rows := linkedRows cursorRefresh 0 ports m source
    after m (eventLog rows) = after m (eventLog source) ∧ rows.length = n ∧
      RAMBuckets.cost Report.probes rows = 20*n := by
  induction n generalizing k m with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n ih =>
    let rep : Report w := ⟨CursorRAM.events pub (Fin.ofNat _ k), some (Fin.ofNat _ (k+1))⟩
    let out := after m rep.events
    obtain ⟨_,hm,_,hp⟩ := activeLinkedReport_effect cursorRefresh 0 ports m rep rfl
    have hprobe : (activeLinkedReport cursorRefresh 0 ports m rep).probes = 19 := hp
    obtain ⟨hmem,hrows,hcost⟩ := ih (k+1) out
    dsimp only
    change after m (eventLog (activeLinkedReport cursorRefresh 0 ports m rep :: _)) =
      after m (eventLog (rep :: _)) ∧ (_ :: _).length = _ ∧ RAMBuckets.cost _ (_ :: _) = _
    refine ⟨?_,?_,?_⟩
    · change after (after m (activeLinkedReport cursorRefresh 0 ports m rep).events)
          (eventLog (linkedRows cursorRefresh 0 ports out (CursorRAM.scanReports pub (k+1) n))) =
        after out (eventLog (CursorRAM.scanReports pub (k+1) n))
      rw [hm]
      exact hmem
    · rw [List.length_cons, hrows]
    · rw [RAMBuckets.cost, hprobe, hcost, Nat.mul_succ]
      omega

/-- Nineteen probes per data call (six writes, twelve frame reads, one tag
read) and fourteen probes for the closing call. Only the latter writes the
tag, and it returns cursor zero. Costs include one unit per call. -/
theorem cursor_pass_effect (ports : Ports w) (pub : Fin 11 → Word w) (k n : ℕ)
    (m : Memory w) :
    let rs := cursorPassReports ports pub k n m
    let sourceMem := after m (eventLog (CursorRAM.scanReports pub k n))
    after m (eventLog rs) = writeMemory sourceMem ports.tag 0 ∧
      endState (some (Fin.ofNat _ k)) rs = some 0 ∧ rs.length = n+1 ∧
      RAMBuckets.cost Report.probes rs = 20*n+15 := by
  let mem := after m (eventLog (CursorRAM.scanReports pub k n))
  let close := closedLinkedReport cursorRefresh 0 ports mem
  obtain ⟨hm,hl,hcost⟩ := linked_cursor_rows ports pub k n m
  obtain ⟨hresult,hmem,_,hp⟩ := closedLinkedReport_effect cursorRefresh 0 ports mem
  dsimp only [cursorPassReports]
  refine ⟨?_,?_,?_,?_⟩
  · simp only [eventLog, List.flatMap_append, after, List.foldl_append]
    change after (after m (eventLog (linkedRows cursorRefresh 0 ports m _))) close.events = _
    rw [hm]
    exact hmem
  · rw [endState_append]; exact hresult
  · rw [List.length_append,hl]; rfl
  · rw [RAMBuckets.cost_append,hcost,RAMBuckets.cost,hp]
    rfl

private theorem column_address {start n t i : ℕ} (room : start + 6*n ≤ 2^w)
    (ht : t < 6) (hi : i < n) :
    start ≤ (CursorRAM.encode w (start+t*n) + CursorRAM.encode w i).val ∧
      (CursorRAM.encode w (start+t*n) + CursorRAM.encode w i).val < start + 6*n := by
  have hoff := CursorRAM.packed_lt ht hi
  have ha : start + t*n+i < 2^w := by omega
  rw [Fin.val_add, Fin.val_ofNat, Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : start+t*n < 2^w),
    Nat.mod_eq_of_lt (by omega : i < 2^w), Nat.mod_eq_of_lt ha]
  omega

section Columns

open CursorRAM CursorNetwork Compression

variable {b l a pad start : ℕ} {S : Type} [Fintype S]
variable (hD : 1 < b+l) (hd : 2+pad = 2^a) (bits : S → ℕ)
local notation "X₀" => cursorState (cursorCoordinateLabels b l) hD hd bits
local notation "N₀" => rowCount b l a
local notation "P₀" => publicWords w b l a (∑ s, bits s) start

private theorem base_address (room : start + 6*N₀ ≤ 2^w) (t : Fin 6) (e : BasePort b l a) :
    let addr := encode w (start + t.val*N₀) + IncidenceDirectory.basePort X₀ e
    start ≤ addr.val ∧ addr.val < start + 6*N₀ := by
  have he : IncidenceDirectory.basePort (w := w) X₀ e = encode w (baseOrder b l a e).val := by
    rw [baseOrder_val]; rfl
  rw [he]
  apply column_address room t.isLt
  exact (baseOrder b l a e).isLt.trans_le
    (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos l)))

private theorem actual_address (room : start + 6*N₀ ≤ 2^w) (t : Fin 6) (e : ActualPort b l a) :
    let addr := encode w (start + t.val*N₀) + IncidenceDirectory.actualPort X₀ e
    start ≤ addr.val ∧ addr.val < start + 6*N₀ := by
  have he : IncidenceDirectory.actualPort (w := w) X₀ e = encode w (actualOrder b l a e).val := by
    rw [actualOrder_val, cursorActualSlotNumber, cursorActualIndex_val]; rfl
  rw [he]
  exact column_address room t.isLt (actualOrder b l a e).isLt

include hD hd

/-- The two base indices and the two actual indices used by a row are port
numbers of the typed graph. Hence even indirect inverse-column writes stay
inside the reserved output region. -/
theorem cursor_write_address (room : start + 6*N₀ ≤ 2^w) {j : ℕ} (hj : j < N₀)
    (av : Word w × Word w) (hav : av ∈ rowWrites P₀ j) :
    start ≤ av.1.val ∧ av.1.val < start + 6*N₀ := by
  let e := (actualOrder b l a).symm ⟨j,hj⟩
  have num : (actualOrder b l a e).val = j := congrArg Fin.val ((actualOrder b l a).apply_symm_apply ⟨j,hj⟩)
  have fit : N₀ < 2^w := by omega
  rw [← num, rowWrites, visit_row hD hd bits start fit e] at hav
  simp only [writes, typedRow, List.mem_cons, List.not_mem_nil, or_false] at hav
  rcases hav with rfl | rfl | rfl | rfl | rfl | rfl
  · exact base_address hD hd bits room 0 _
  · exact base_address hD hd bits room 1 _
  · exact base_address hD hd bits room 2 _
  · exact column_address room (t := 3) (by decide) (actualOrder b l a e).isLt
  · exact actual_address hD hd bits room 4 _
  · exact column_address room (t := 5) (by decide) (actualOrder b l a e).isLt

/-- Natural-address layout conditions suffice for the complete cursor scan.
The frame may be placed on either side of the incidence columns. -/
theorem cursor_disjoint_layout (ports : Ports w) (room : start + 6*N₀ ≤ 2^w)
    (tag : ports.tag.val < start ∨ start + 6*N₀ ≤ ports.tag.val)
    (frame : ports.activeFrame.val + 12 ≤ start ∨ start + 6*N₀ ≤ ports.activeFrame.val)
    (frameFits : ports.activeFrame.val + 12 ≤ 2^w) : CursorDisjoint ports P₀ 0 N₀ := by
  intro j _ hj av ha
  obtain ⟨lo,hi⟩ := cursor_write_address hD hd bits room (by simpa using hj) av ha
  refine ⟨fun he ↦ ?_, fun u he ↦ ?_⟩
  · rw [he] at lo hi
    omega
  · have hu := u.isLt
    have hu' : (u.val : Word w).val = u.val := Nat.mod_eq_of_lt (by omega)
    have haddr : (ports.activeFrame + (u.val : Word w)).val = ports.activeFrame.val + u.val := by
      rw [Fin.val_add, hu', Nat.mod_eq_of_lt (by omega)]
    rw [he, haddr] at lo hi
    omega

/-- The closing transfer can write its tag after the scan without changing
any of the six typed incidence tables. -/
theorem cursor_directory_write_tag (room : start + 6*N₀ ≤ 2^w) (tag v : Word w)
    (htag : tag.val < start ∨ start + 6*N₀ ≤ tag.val) {m : Memory w}
    (rep : (directory w b l a start).Represents X₀ m) :
    (directory w b l a start).Represents X₀ (writeMemory m tag v) := by
  have eq (addr : Word w) (h : start ≤ addr.val ∧ addr.val < start + 6*N₀) :
      writeMemory m tag v addr.val = m addr.val := ite_eq_right (by omega)
  constructor
  · intro e
    exact (eq _ (base_address hD hd bits room 0 e)).trans (rep.baseOut e)
  · intro e
    exact (eq _ (base_address hD hd bits room 1 e)).trans (rep.baseIn e)
  · intro e
    exact (eq _ (base_address hD hd bits room 2 e)).trans (rep.shift e)
  · intro e
    exact (eq _ (actual_address hD hd bits room 3 e)).trans (rep.actualOut e)
  · intro e
    exact (eq _ (actual_address hD hd bits room 4 e)).trans (rep.actualIn e)
  · intro e
    exact (eq _ (actual_address hD hd bits room 5 e)).trans (rep.width e)

/-- The native linked worker builds the level-zero cursor directory and
returns the dispatcher to its controller. The protected frame may be before
or after the columns. The tag and frame are read from the supplied memory. -/
theorem initialize_linked_cursor (controller : Template p r 5) (ports : Ports w) (m : Memory w)
    (room : start + 6*N₀ ≤ 2^w) (widthFits : (∑ s, bits s) < 2^w)
    (tag : ports.tag.val < start ∨ start + 6*N₀ ≤ ports.tag.val)
    (frame : ports.activeFrame.val + 12 ≤ start ∨ start + 6*N₀ ≤ ports.activeFrame.val)
    (frameFits : ports.activeFrame.val + 12 ≤ 2^w)
    (hready : Ready cursorRefresh 0 ports P₀ (encode w N₀) m)
    {cap : ℕ} (hcap : 119 ≤ cap) :
    let D := (machine cursorRefresh controller ports).program
    let rs := cursorPassReports ports P₀ 0 N₀ m
    let out := after m (eventLog rs)
    runSegment D cap (some 0) m (List.replicate N₀ [] ++ [[]]) = some rs ∧
      (directory w b l a start).Represents X₀ out ∧
      out ports.tag.val = 0 ∧ endState (some 0) rs = some 0 ∧
      rs.length = N₀+1 ∧ RAMBuckets.cost Report.probes rs = 20*N₀+15 := by
  have hp : 0 < N₀ := by unfold rowCount; positivity
  have hv : (encode w N₀).val = N₀ := Nat.mod_eq_of_lt (by omega)
  have hsep := cursor_disjoint_layout hD hd bits ports room tag frame frameFits
  have hrun := cursor_segment controller ports P₀ 0 N₀ m (encode w N₀) (by omega) hready hsep
    (by omega) hcap []
  have hrep := (initialize_cursor hD hd bits room widthFits m).2.1
  obtain ⟨hmem, hres, hlen, hcost⟩ := cursor_pass_effect ports P₀ 0 N₀ m
  dsimp only
  refine ⟨?_, ?_, ?_, hres, hlen, hcost⟩
  · simpa only [runSegment, Option.map_some, List.append_nil, Fin.ofNat_eq_cast, Nat.cast_zero] using hrun
  · rw [hmem]
    exact cursor_directory_write_tag hD hd bits room ports.tag 0 tag hrep
  · rw [hmem]
    simp [writeMemory]

end Columns

end CompressorRecords.Schedule

end VPVNP
end Computability
end OAI
