import OAI.Computability.VPVNP.CompressorShrinkSlotScheduledRuns
import OAI.Computability.VPVNP.CompressorLogAccess

/-!
# External accesses in the shrinking slot preparation and column copies

Every preparation call has one external write and no reads. Each copy call
reads one live source cell and writes the corresponding destination cell.
The resulting bounds apply to every individual source segment of the
twenty-two-visit program when the directory and output scans have their
respective event bounds.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM SourceTransport
open scoped Fin.CommRing
open private addr_val from OAI.Computability.VPVNP.CompressorLogAccess

variable {w : ℕ}

namespace ShrinkSlots.Preparation

open SlotLevel SlotOwners

/-- All seven preparation phases access only their output cells. The stronger
upper bound is the start of the sorted rows, immediately after the counters. -/
theorem Reports.Native.footprint {r : Reports w} {s : Shape} {h : Heads} {layout : Bool} {m : Memory w}
    (native : r.Native s h layout m) (roleRoom : h.role+8 ≤ h.nextSite)
    (nextRoom : h.nextSite+sites s ≤ h.subdivisions) (subRoom : h.subdivisions+4 ≤ h.scratch)
    (fit : rowsHead s h < 2^w) :
    LogAccess (fun _ ↦ False) (fun x ↦ h.role ≤ x ∧ x < rowsHead s h) r.all := by
  obtain ⟨hp,hr,hn,hc⟩ := native
  let cnt := owners s+fields s
  let clearHead := h.scratch+fields s
  have endEq : rowsHead s h = clearHead+cnt := rfl
  have low : h.scratch ≤ clearHead := Nat.le_add_right ..
  have pub : LogAccess (fun _ ↦ False) (fun x ↦ h.role ≤ x ∧ x < rowsHead s h) (List.ofFn r.publish) := by
    have same (i : Fin 4) := Option.some.inj ((hp i).symm.trans (publish_run h.subdivisions s.subdivisions
      (after m (eventLog ((List.ofFn r.publish).take i.val))) i))
    have one (i : Fin 4) : LogAccess (fun _ ↦ False) (fun x ↦ h.role ≤ x ∧ x < rowsHead s h) [r.publish i] := by
      rw [(List.cons.inj (same i)).1]
      change Reads _ (directEvents 3 2 _ _) ∧ Writes _ (directEvents 3 2 _ _)
      apply direct_events
      have ht := i.isLt
      change h.role ≤ (h.subdivisions+i.val) % (2^w) ∧ (h.subdivisions+i.val) % (2^w) < rowsHead s h
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    exact (((one 0).append (one 1)).append (one 2)).append (one 3)
  have roles := direct_scan _ 26 23 1 h.role 8 (Aux.roleValue ((roleBank h layout w) 0))
    (by omega) (Aux.role_native (roleBank h layout w)) _ _ hr
  have cyclic := direct_scan _ 19 16 1 h.nextSite (sites s) (Aux.nextValue (cyclicBank s h w))
    (by omega) (Aux.next_native (cyclicBank s h w)) _ _ hn
  have clear := direct_scan _ 8 4 2 clearHead cnt (fun _ ↦ (0 : Word w)) (by omega)
    (fun mem i ↦ SliceRAM.clearVisit_native (clearHead : Word w) i mem) _ _ hc
  exact ((pub.append (roles.mono (fun _ hx ↦ hx) (fun _ hx ↦ by obtain ⟨_,_⟩ := hx; omega))).append
    (cyclic.mono (fun _ hx ↦ hx) (fun _ hx ↦ by obtain ⟨_,_⟩ := hx; omega))).append
    (clear.mono (fun _ hx ↦ hx) (fun _ hx ↦ by obtain ⟨_,_⟩ := hx; omega))

end ShrinkSlots.Preparation

namespace CopyIncidence

open Compression

/-- Natural half-open intervals of the six live columns. -/
def ColumnCell {a l : ℕ} (Y : State a l) (T : IncidenceDirectory w) (x : ℕ) : Prop :=
  ∃ c, (T.column c).val ≤ x ∧ x < (T.column c).val+rows Y c

private def copyEvents (src dst i : Word w) (m : Memory w) : List (Event w) :=
  [.tick,.tick,.tick,.tick,.tick,.read (src+i) (m (src+i).val),.tick,.tick,
    .write (dst+i) (m (src+i).val),.tick,.tick]

private theorem copy_events_native (src dst i : Word w) (m : Memory w) :
    let M := (copyPass.table.instantiate w (copyPublic src dst)).program
    execute M 12 (M.start i) m [] = some ⟨copyEvents src dst i m,some (i+1)⟩ := by
  change execute ((template LiveAuxiliaryHeaders.copyWord 7).instantiate w (copyPublic src dst)).program
    (1+LiveAuxiliaryHeaders.copyWord.length) ⟨_,i,fun _ ↦ 0,fun _ ↦ 0⟩ m [] = _
  rw [execute_template,run_eq_trace]
  simp (config := {decide := true}) [LiveAuxiliaryHeaders.copyWord,trace,Op.effect,Function.update,copyPublic,
    copyEvents,BinaryOp.eval]

private theorem column_val (base : Word w) (i : ℕ) (fit : base.val+i < 2^w) :
    (base+(i : Word w)).val = base.val+i := by
  have hb : (base.val : Word w) = base := Fin.ext (Nat.mod_eq_of_lt base.isLt)
  simpa only [hb] using addr_val (w := w) base.val i fit

/-- Every copied report reads the selected source column at its own ordinal
and writes only the same ordinal in the corresponding destination column. -/
theorem Runs.footprint {a l : ℕ} {Y : State a l} {T U : IncidenceDirectory w} {cs : List (Fin 6)}
    {m : Memory w} {rs : List (Report w)} (run : Runs Y T U cs m rs)
    (roomT : ∀ c, (T.column c).val+rows Y c ≤ 2^w) (roomU : ∀ c, (U.column c).val+rows Y c ≤ 2^w) :
    LogAccess (ColumnCell Y T) (ColumnCell Y U) rs := by
  induction run with
  | nil => exact ⟨fun _ _ h ↦ (List.not_mem_nil h).elim,fun _ _ h ↦ (List.not_mem_nil h).elim⟩
  | cons c hr _ ih =>
    refine LogAccess.append ?_ ih
    let src := T.column c
    let dst := U.column c
    let ev := fun m i ↦ copyEvents src dst i m
    refine (StageFrame.scan _ 12 0 (rows Y c) (fun _ _ ↦ True) ev _ _
      (fun _ _ _ m ↦ copy_events_native src dst _ m) ?_ (Nat.zero_le _) _ _
      trivial (by simpa only [Nat.sub_zero,Nat.cast_zero] using hr)).2.2
    intro j _ hj _ _
    have addr (D : IncidenceDirectory w) (room : (D.column c).val+rows Y c ≤ 2^w) :
        ColumnCell Y D (D.column c+(j : Word w)).val := by
      refine ⟨c,?_⟩
      rw [column_val _ _ (by omega)]
      omega
    refine ⟨trivial,?_,?_⟩
    · intro x v hx; simp [ev,copyEvents] at hx
      exact hx.1 ▸ addr T (roomT c)
    · intro x v hx; simp [ev,copyEvents] at hx
      exact hx.1 ▸ addr U (roomU c)

end CopyIncidence

/-- An aggregate event bound on a chronological walk also holds at each
source stage in its own memory. -/
theorem SourceWalk.refine_footprints {J : Type*} {src : J → Memory w → List (Report w) → Prop}
    {stages : List J} {m : Memory w} {rs : List (Report w)} {rd wr : ℕ → Prop}
    (walk : SourceWalk src stages m rs) (bounds : LogAccess rd wr rs) :
    SourceWalk (fun j m rs ↦ src j m rs ∧ LogAccess rd wr rs) stages m rs := by
  induction walk with
  | done => exact .done _
  | next head _ ih =>
    simp only [LogAccess,eventLog,List.flatMap_append] at bounds
    exact .next ⟨head,fun a v h ↦ bounds.1 a v (List.mem_append_left _ h),
      fun a v h ↦ bounds.2 a v (List.mem_append_left _ h)⟩ (ih ⟨fun a v h ↦ bounds.1 a v (List.mem_append_right _ h),
      fun a v h ↦ bounds.2 a v (List.mem_append_right _ h)⟩)

namespace ShrinkSlotPlan.Scheduled

open ShrinkSlots SlotLevel Compression

/-- Combine the concrete preparation and copy accesses with the five directory
and four output scans. Each of the twenty-two stages retains its own source
execution and bounds on its own read and write events. -/
theorem sources_with_footprints {a l : ℕ} (P : Plan) (s : Shape) (h : Heads) (chosen : Bool)
    (splitHead : ℕ) (dest : IncidenceDirectory w) (Y : State a l)
    (r : Build.Construction w) (m : Memory w) (hr : r.Native s h splitHead chosen m)
    (lengths : ∀ c, CopyIncidence.rows Y c = (Stage.copy c).limit s)
    (roleRoom : h.role+8 ≤ h.nextSite) (nextRoom : h.nextSite+sites s ≤ h.subdivisions)
    (subRoom : h.subdivisions+4 ≤ h.scratch) (fit : rowsHead s h < 2^w)
    (roomT : ∀ c, ((directory s h w).column c).val+CopyIncidence.rows Y c ≤ 2^w)
    (roomU : ∀ c, (dest.column c).val+CopyIncidence.rows Y c ≤ 2^w)
    (rd wr : ℕ → Prop)
    (prepRegion : ∀ x, h.role ≤ x → x < rowsHead s h → wr x)
    (sourcesRead : ∀ x, CopyIncidence.ColumnCell Y (directory s h w) x → rd x)
    (destWrite : ∀ x, CopyIncidence.ColumnCell Y dest x → wr x)
    (core : LogAccess rd wr r.passes.slots.all)
    (out : LogAccess rd wr (r.passes.mates.all++r.passes.widths)) :
    let built := after m (eventLog r.all)
    let copies := CopyIncidence.reports Y (directory s h w) dest CopyIncidence.allColumns built
    SourceWalk (fun j m rs ↦ Source P s h chosen splitHead dest j m rs ∧ LogAccess rd wr rs)
      order m (r.all++copies) := by
  intro built copies
  have prep := hr.1.footprint roleRoom nextRoom subRoom fit
  have copied := CopyIncidence.reports_run Y (directory s h w) dest CopyIncidence.allColumns built
  have copy := copied.footprint roomT roomU
  have pass : LogAccess rd wr r.passes.all := by
    simpa only [Build.Passes.all,List.append_assoc] using core.append out
  exact ((construction_sources P s h chosen splitHead dest r m hr).append
    (copy_sources P s h chosen splitHead dest Y lengths copied)).refine_footprints
    (((prep.mono (fun _ ↦ False.elim) (fun x hx ↦ prepRegion x hx.1 hx.2)).append pass).append
      (copy.mono sourcesRead destWrite))

end ShrinkSlotPlan.Scheduled

end CompressorRecords

end VPVNP
end Computability
end OAI
