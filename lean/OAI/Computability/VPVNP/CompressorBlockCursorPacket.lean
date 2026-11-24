import OAI.Computability.VPVNP.CompressorBlockHeaderPacket
import OAI.Computability.VPVNP.CompressorBlockHeaderStartup
import OAI.Computability.VPVNP.CompressorRecordsScheduleCursor

/-!
# Cursor incidence as the third source packet of the block program

The worker reads its eleven operands from the published first-level frame.
It starts at zero, returns each following row index, and writes all six
incidence columns for the actual cursor state. Every address before the
columns retains its incoming value.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BlockCursorPacket

open CursorNetwork BurstRAM BlockPlanner BlockHeaderRun BlockHeaderStartup DescriptorSpace CursorRAM SourceTransport
open scoped Fin.CommRing

variable {w : ℕ}

private theorem row_events (p : Fin 11 → Word w) (i : ℕ) (x v : Word w) :
    (.read x v : Event w) ∉ events p (Fin.ofNat _ i) ∧
      (.write x v ∈ events p (Fin.ofNat _ i) → (x,v) ∈ rowWrites p i) := by
  simp [events,rowWrites,writes]

private theorem scan_access (p : Fin 11 → Word w) (k n : ℕ) (data : ℕ → Prop)
    (ok : ∀ j, k ≤ j → j < k+n → ∀ av ∈ rowWrites p j, data av.1.val) :
    Reads (fun _ ↦ False) (eventLog (scanReports p k n)) ∧ Writes data (eventLog (scanReports p k n)) := by
  induction n generalizing k with
  | zero => exact ⟨fun _ _ h ↦ False.elim (List.not_mem_nil h),fun _ _ h ↦ False.elim (List.not_mem_nil h)⟩
  | succ n ih =>
    obtain ⟨rd,wr⟩ := ih (k+1) (fun j lo hi av mem ↦ ok j (by omega) (by omega) av mem)
    constructor
    · intro x v mem
      rcases List.mem_append.mp mem with h|h
      · exact (row_events p k x v).1 h
      · exact rd x v h
    · intro x v mem
      rcases List.mem_append.mp mem with h|h
      · exact ok k le_rfl (by omega) (x,v) ((row_events p k x v).2 h)
      · exact wr x v h

private theorem scan_progress (p : Fin 11 → Word w) (k n : ℕ) (fit : k+n < 2^w) :
    SourceOnline.Progress ((k+n : ℕ) : Word w) (Fin.ofNat _ k) (scanReports p k n) := by
  induction n generalizing k with
  | zero => exact .done le_rfl
  | succ n ih =>
    have bound : (k+1)+n = k+(n+1) := by omega
    refine SourceOnline.Progress.next (next := Fin.ofNat _ (k+1)) ?_ rfl ?_
    · apply Fin.lt_def.mpr
      rw [Fin.val_ofNat,Fin.val_natCast,Nat.mod_eq_of_lt (show k < 2^w by omega),Nat.mod_eq_of_lt fit]
      omega
    · exact bound ▸ ih (k+1) (by omega)

variable {a b l pad : ℕ} {T : Type} [Fintype T]

open Compression in
/-- The scan follows the two raw header publishers. Its report list certifies
the exact typed outgoing, incoming, displacement and width records, including
the incoming entries written at computed destination indices. -/
theorem run (L : Layout) (n : ℕ) (base : Word w) (m : Memory w) (s : Word w)
    (hD : 1 < b+l) (hd : 2+pad = 2^a) (bits : T → ℕ)
    (ready : BlockHeaderStartup.Ready L a b l (∑ t, bits t) n base m)
    (room : incidenceStart L 0+6*rowCount b l a ≤ 2^w) (width : (∑ t, bits t) < 2^w) :
    let W := ∑ t, bits t
    let pub := (Workspace.ports L.shape.arity base).data
    let mem := initialFinal a L m
    let start := incidenceStart L 0
    let p := publicWords w b l a W start
    let N := rowCount b l a
    let rs := scanReports p 0 N
    let out := after mem (eventLog rs)
    let X := cursorState (cursorCoordinateLabels b l) hD hd bits
    HeaderPacket.Run L pub s (BlockPlanner.cursor BlockHeaderPlan.persistentFrame) mem rs
      (1+visit.length) (List.replicate N []) ∧
      (directory w b l a start).Represents X out ∧
      (∀ x, x < start ∨ start+6*N ≤ x → out x = mem x) ∧
      rs.length = N ∧ RAMBuckets.cost Report.probes rs = 7*N := by
  intro W pub mem start p N rs out X
  obtain ⟨native,rep,_,len,_,cost,_⟩ := initialize_cursor hD hd bits room width mem
  obtain ⟨stop,params⟩ := ready.initial.cursor pub s (ready.first s) ready.count_before ready.frame
  change (BlockPlanner.cursor BlockHeaderPlan.persistentFrame).stop.eval pub s mem = (N : Word w) at stop
  change (fun j ↦ ((BlockPlanner.cursor BlockHeaderPlan.persistentFrame).params j).eval pub s mem) = p at params
  have touched (j : ℕ) (hj : j < N) (av : Word w × Word w) (ha : av ∈ rowWrites p j) :
      start ≤ av.1.val ∧ av.1.val < start+6*N :=
    Schedule.cursor_write_address hD hd bits room hj av ha
  obtain ⟨rd,wr⟩ := scan_access p 0 N (fun x ↦ start ≤ x ∧ x < start+6*N)
    (fun j _ hj av ha ↦ touched j (by simpa using hj) av ha)
  have hstart : levelStart L 0 ≤ start := Nat.le_add_right ..
  have hN : N < 2^w := by
    change incidenceStart L 0 + 6*N ≤ 2^w at room
    have pos : 0 < N := by dsimp [N,rowCount]; positivity
    omega
  refine ⟨⟨by omega,?_,?_,fun x v hv ↦ (rd x v hv).elim,fun x v hv ↦ hstart.trans (wr x v hv).1⟩,
    rep,?_,len,cost⟩
  · let executeBank := fun data : Fin 11 → Word w ↦
      runSegment ((PrimedStackRAM.template CursorRAM.visit 0).instantiate w data).program (1+visit.length)
        (some (encode w 0)) mem (List.replicate N [])
    exact (congrArg executeBank params).trans native
  · rw [stop]
    change SourceOnline.Progress (N : Word w) (Fin.ofNat _ 0) (scanReports p 0 N)
    simpa only [Nat.zero_add] using scan_progress p 0 N (by simpa only [Nat.zero_add] using hN)
  · intro x hx
    apply after_outside mem wr
    omega

end CompressorRecords.BlockCursorPacket

end VPVNP
end Computability
end OAI
