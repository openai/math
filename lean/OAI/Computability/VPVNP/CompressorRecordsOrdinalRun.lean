import OAI.Computability.VPVNP.CompressorRecordsDirectory

/-!
# Ordinal worker scans inside the guarded compressor dispatcher

A worker may return a dense ordinal, a strided address, or another
computed cursor. At each genuine source call its result advances to the
next cursor and its writes preserve the active frame and control cells.
These properties turn the raw segment into the guarded trace used by
the online launcher, while retaining the worker's own graph invariant.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.OrdinalRun

open BurstRAM Schedule
open scoped Fin.CommRing

variable {d w : ℕ} (C : Catalog d) (worker : Fin d) (ports : Ports w)

/-- Mutable control cells and every word read from the active worker frame. -/
def ControlCell (params : ℕ) (ports : Ports w) (x : ℕ) : Prop :=
  x = ports.tag.val ∨ x = ports.ordinal.val ∨ x = ports.rows.val ∨
    ∃ j : Fin (params+1), x = (ports.activeFrame+(j.val : Word w)).val

/-- The two memories agree on the stage tag, ordinal, row count, and the active frame's
stopping cursor and parameter words. -/
def Preserved (params : ℕ) (ports : Ports w) (before after : Memory w) : Prop :=
  ∀ x, ControlCell params ports x → after x = before x

theorem ready_of_preserved {pub : Fin (C worker).params → Word w} {stop : Word w} {mem next : Memory w}
    (ready : Ready C worker ports pub stop mem) (stable : Preserved (C worker).params ports mem next) :
    Ready C worker ports pub stop next := by
  refine ⟨(stable _ (.inl rfl)).trans ready.1,?_,?_⟩
  · have h := stable _ (.inr (.inr (.inr ⟨0, rfl⟩)))
    change next (ports.activeFrame+(0 : Word w)).val = mem (ports.activeFrame+(0 : Word w)).val at h
    simpa only [add_zero,stopWord] using h.trans (by simpa only [add_zero,stopWord] using ready.2.1)
  · funext j
    exact (stable _ (.inr (.inr (.inr ⟨j.succ,rfl⟩)))).trans (congrFun ready.2.2 j)

/-- Check all dispatch guards from a genuine raw execution. The ordinal
invariant may describe already written fields as well as future inputs.
Every control cell has its initial value at the end of the scan. -/
theorem validTrace {Q : Type*} (P : BurstRAM.Program w Q) (fuel : ℕ) (pub : Fin (C worker).params → Word w)
    (stop : Word w) (cursor : ℕ → Word w) (N : ℕ) (I : ℕ → Memory w → Prop)
    (active : ∀ j < N, cursor j < stop) (closed : stop ≤ cursor N)
    (advance : ∀ j < N, ∀ mem, I j mem → ∀ bits rep,
      execute P fuel (P.start (cursor j)) mem bits = some rep →
      rep.result = some (cursor (j+1)) ∧ I (j+1) (after mem rep.events) ∧
        Preserved (C worker).params ports mem (after mem rep.events))
    (j : ℕ) (bs : List (List Bool)) (mem : Memory w) (rs : List (Report w))
    (size : j+bs.length = N) (inv : I j mem) (ready : Ready C worker ports pub stop mem)
    (run : runSegment P fuel (some (cursor j)) mem bs = some rs) :
    ValidTrace C worker ports pub stop (cursor j) mem rs ∧
      I N (after mem (eventLog rs)) ∧ Preserved (C worker).params ports mem (after mem (eventLog rs)) := by
  induction bs generalizing j mem rs with
  | nil =>
    change some [] = some rs at run
    cases Option.some.inj run
    change j+0 = N at size
    have e : j=N := by omega
    subst j
    exact ⟨⟨ready,closed⟩,inv,fun _ _ => rfl⟩
  | cons b bs ih =>
    cases h : execute P fuel (P.start (cursor j)) mem b with
    | none => simp [runSegment,h] at run
    | some rep =>
      have hj : j<N := by rw [List.length_cons] at size; omega
      obtain ⟨inc,inv',keep⟩ := advance j hj mem inv b rep h
      simp only [runSegment,h,inc,Option.map_eq_some_iff] at run
      obtain ⟨tail,rt,rfl⟩ := run
      let mid := after mem rep.events
      obtain ⟨trace,last,frame⟩ := ih (j+1) mid tail (by rw [List.length_cons] at size; omega)
        inv' (ready_of_preserved C worker ports ready keep) rt
      have post : after mem (eventLog (rep :: tail)) = after mid (eventLog tail) := by
        change (rep.events ++ eventLog tail).foldl BurstRAM.update mem = _
        rw [List.foldl_append]; rfl
      rw [post]
      exact ⟨⟨ready,active j hj,cursor (j+1),inc,trace⟩,last,fun x hx => (frame x hx).trans (keep x hx)⟩

/-- Specialization to an already prepared physical directory row. -/
theorem row_valid (row : Directory.Row d w) (cursor : ℕ → Word w) (I : ℕ → Memory w → Prop)
    (start : Directory.start C ports row.input = cursor 0)
    (active : ∀ j < row.choices.length, cursor j < Directory.bound C ports row.input)
    (closed : Directory.bound C ports row.input ≤ cursor row.choices.length)
    (tag : row.input ports.tag.val = 0) (live : row.input ports.ordinal.val < row.input ports.rows.val)
    (fuel : 0 < row.fuel)
    (ready : Ready C row.worker ports (Directory.words C ports row.worker row.input)
      (Directory.bound C ports row.input) (row.dataMemory C ports))
    (inv : I 0 (row.dataMemory C ports))
    (run : let P := ((C row.worker).table.instantiate w (Directory.words C ports row.worker row.input)).program
      runSegment P row.fuel (some (cursor 0)) (row.dataMemory C ports) row.choices = some row.reports)
    (advance : let P := ((C row.worker).table.instantiate w (Directory.words C ports row.worker row.input)).program
      ∀ j < row.choices.length, ∀ mem, I j mem → ∀ bits rep, execute P row.fuel (P.start (cursor j)) mem bits = some rep →
        rep.result = some (cursor (j+1)) ∧ I (j+1) (after mem rep.events) ∧
          Preserved (C row.worker).params ports mem (after mem rep.events)) :
    row.Valid C ports ∧ I row.choices.length (row.endMemory C ports) ∧
      Preserved (C row.worker).params ports (row.dataMemory C ports) (row.endMemory C ports) := by
  let P := ((C row.worker).table.instantiate w (Directory.words C ports row.worker row.input)).program
  obtain ⟨frame,last,keep⟩ := validTrace C row.worker ports P row.fuel _ _ cursor _ I active closed advance 0 _ _ _
    (Nat.zero_add _) inv ready run
  exact ⟨⟨tag,live,fuel,start ▸ run,start ▸ frame⟩,last,keep⟩

end CompressorRecords.OrdinalRun

end VPVNP
end Computability
end OAI
