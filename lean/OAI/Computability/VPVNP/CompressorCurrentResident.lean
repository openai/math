import OAI.Computability.VPVNP.CompressorCurrentGraphFrame
import OAI.Computability.VPVNP.CompressorCurrentGraphInitial
import OAI.Computability.VPVNP.CompressorSelectedDirectoryHistory
import OAI.Computability.VPVNP.CompressorScheduledTraceData

/-!
# The graph and selected directory history at a calendar boundary

At each selected pass, the resident memory contains both the earlier
placement directories and the six incidence columns of the current graph.
Publishing the pass adds its occurrence to the history and installs the next
graph. Agreement on the data region carries both records to the memory of
the scheduled online worker.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.CurrentResident

open BurstRAM Compression DescriptorSpace PairSimulation.LocalHistory PairSimulation.TraversalRows
open PairSimulation.TraversalRoles BlockHeaderRun
open scoped Fin.CommRing
open private fit_fields from OAI.Computability.VPVNP.CompressorBlockHeaderRun

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f) {w : ℕ}

/-- The current level index is the number of previously selected passes. -/
def resident (initial : TaggedLayer) (L : Layout) (base n : ℕ) (initialFrame : Fin 8 → Word w) :
    ScheduledTrace.Resident B f hf w :=
  fun past {_ _} X m =>
    SelectedDirectoryHistory.Prefix B f hf initial L base past X m ∧
    CurrentGraph.Current L past.length X n m ∧ Frame.data (header w L 0 + 6) m = initialFrame

variable {B f hf} {initial : TaggedLayer} {L : Layout} {base n a g : ℕ}
variable {initialFrame : Fin 8 → Word w} {past : List (SelectedLevel B f hf)}
variable {X : State a g} {m out : Memory w}

/-- Level zero starts at the cursor layer and at the published DFS base. -/
theorem empty (cur : CurrentGraph.Current L 0 X n m) (role : m (levelStart L 0 + 27) = 0)
    (frame : Frame.data (header w L 0 + 6) m = initialFrame) :
    resident B f hf ⟨leafLayer (siteOrder X), .cursor⟩ L (endAddress L) n initialFrame [] X m := by
  have word : m (levelStart L 0 + 14) = (endAddress L : Word w) := by
    apply Fin.ext
    rw [Fin.val_natCast, ← cur.startup.arena, Nat.mod_eq_of_lt (m _).isLt]
  exact ⟨SelectedDirectoryHistory.Prefix.empty word role, cur, frame⟩

/-- The cursor publisher initializes all three resident records in the
actual post-memory of the linked four-row interval. -/
theorem initial_live {b width : ℕ} {workspace : Word w}
    (cursor : BlockStartupPrefix.Resident L a b g width n workspace m X)
    (agree : SourceTransport.Agree (levelStart L 0 ≤ ·)
      (BlockInitialPackets.post L a b g width m) out)
    (positive : 0 < L.levels) (fields : 14 ≤ L.shape.scalarFields) (fit : endAddress L < 2 ^ w) :
    resident B f hf ⟨leafLayer (siteOrder X), .cursor⟩ L (endAddress L) n
      (CursorRAM.ScheduleInit.inputs (CursorRAM.encode w (directoryBase L)) (CursorRAM.encode w 1)
        b g a width (incidenceStart L 0)) [] X out := by
  obtain ⟨cur, frame, role⟩ := cursor.current_live out agree positive fields fit
  exact empty cur role frame

/-- Scheduler traffic below the first level leaves every recorded directory
and every current-state field intact. -/
theorem transfer (h : resident B f hf initial L base n initialFrame past X m)
    (index : past.length < L.levels)
    (fit : endAddress L < 2 ^ w) (fields : 14 ≤ L.shape.scalarFields)
    (slots : IncidenceDirectory.slotCount X ≤ slotCapacity L)
    (agree : SourceTransport.Agree (levelStart L 0 ≤ ·) m out) :
    resident B f hf initial L base n initialFrame past X out := by
  have pos : 0 < L.levels := (Nat.zero_le _).trans_lt index
  have room := fit_fields L ⟨0, pos⟩ fit
  change levelStart L 0 + L.shape.scalarFields < 2 ^ w at room
  exact ⟨h.1.transfer agree,
    CurrentGraph.Current.transfer (i := ⟨past.length, index⟩) h.2.1 fit (by omega) slots agree,
    (CurrentGraph.frame_transfer (by omega) agree).trans h.2.2⟩

/-- Append one selected occurrence. Its output incidence data and its
history directory are read at the same post-memory. -/
theorem append {v : SelectedLevel B f hf}
    (h : resident B f hf initial L base n initialFrame past v.input m)
    (emission : SelectedDirectoryHistory.Emission L past.length v m out)
    (wide : 28 ≤ levelWords L) (room : levelStart L (past.length + 1) ≤ base)
    (previous : ∀ x, levelsBase L ≤ x → x < levelStart L past.length → out x = m x)
    (next : CurrentGraph.Current L (past.length + 1) (v.pass.next v.term) n out)
    (frame : Frame.data (header w L 0 + 6) out = initialFrame) :
    resident B f hf initial L base n initialFrame (past ++ [v]) (v.pass.next v.term) out := by
  exact ⟨h.1.append emission wide room previous,
    by simpa only [List.length_append, List.length_singleton] using next, frame⟩

/-- Recover the next resident graph from the concrete scalar substep, six
new incidence columns, the emitted traversal directory, and the physical
memory frame of this pass. -/
theorem append_substep {v : SelectedLevel B f hf} (old new : Fin L.levels)
    (oldAt : past.length = old.val) (newAt : old.val + 1 = new.val)
    (h : resident B f hf initial L (endAddress L) n initialFrame past v.input m)
    (fields : 30 ≤ L.shape.scalarFields) (fit : endAddress L < 2 ^ w)
    (sub : Substep v L old new (by omega) m)
    (emission : SelectedDirectoryHistory.Emission L past.length v m out)
    (columns : (packedIncidence L w new
      (IncidenceDirectory.slotCount (v.pass.next v.term))).Represents
      (v.pass.next v.term) out)
    (graph : ∀ x, CurrentGraph.graphCell L new x ∨ CurrentGraph.startupCell L x
      ∨ CurrentGraph.frameCell L x →
      out x = finalMemory v L old new m x)
    (previous : ∀ x, levelsBase L ≤ x → x < levelStart L past.length → out x = m x) :
    resident B f hf initial L (endAddress L) n initialFrame (past ++ [v])
      (v.pass.next v.term) out := by
  have current : CurrentGraph.Current L old v.input n m := by rw [← oldAt]; exact h.2.1
  have successor := current.successor v old new newAt fields fit sub columns
    (fun x hx => graph x (hx.imp_right Or.inl))
  have index : past.length + 1 = new.val := by omega
  have wide : 28 ≤ levelWords L := by unfold levelWords levelHeaderWords; omega
  have room := levelStart_mono L
    (show past.length + 1 ≤ L.levels from by rw [index]; exact new.isLt.le)
  have pos : 0 < L.levels := (Nat.zero_le _).trans_lt old.isLt
  have span := fit_fields L ⟨0, pos⟩ fit
  change levelStart L 0 + L.shape.scalarFields < 2 ^ w at span
  apply append h emission wide room previous (by rw [index]; exact successor)
  exact (CurrentGraph.frame_keep (by omega) (fun x hx => graph x (.inr (.inr hx)))).trans
    ((CurrentGraph.frame_publish v sub newAt (by omega) fit).trans h.2.2)

end CompressorRecords.CurrentResident

end VPVNP
end Computability
end OAI
