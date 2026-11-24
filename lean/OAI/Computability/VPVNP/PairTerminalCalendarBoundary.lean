import OAI.Computability.VPVNP.PairTerminalSelectedReady
import OAI.Computability.VPVNP.CompressorCurrentResident

/-!
# The terminal bootstrap and prefix from the completed calendar boundary

The selected graph, placement history, saved cursor parameters and online
row count all belong to the same final boundary. The four initial visits
establish this invariant for zero compression blocks. Each executed substep
extends it with the new graph and its placement directory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalPrefix.Linked

open BurstRAM PrivateRAM Compression CompressorRecords DescriptorSpace LocalHistory
open TraversalRows TerminalBootstrap TerminalLink ScheduledTrace
open scoped Fin.CommRing

variable {w : ℕ} {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f) {n : ℕ}
variable (T : ℕ) (hT : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
variable (z : (B.execute f hf T hT X).Choices)
variable (positions baseBits laneBits width inputN : ℕ) (pub : Fin 11 → Word w)
set_option quotPrecheck false in
local notation "L" => BlockProgram.layout B (pub 2).val positions T
local notation "ls" => selectedLayers B f hf T hT X z
local notation "vs" => executeLevels B f hf T hT X z
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z
local notation "saved" => CursorRAM.ScheduleInit.inputs (CursorRAM.encode w (directoryBase L))
  (CursorRAM.encode w 1) baseBits laneBits (S.degreeExponent 0) width (incidenceStart L 0)
set_option quotPrecheck false in
local notation "resident" => CurrentResident.resident B f hf ⟨leafLayer (siteOrder X), .cursor⟩
  L (endAddress L) inputN saved
set_option quotPrecheck false in
local notation "tab" => (⟨0, by change 0 < 6; decide⟩ : Fin (L).shape.tables)
set_option quotPrecheck false in
local notation "Aₜ" => fromState L (ls).dropLast B.recordLimit baseBits laneBits (Y) tab

private theorem slot_count {a l : ℕ} (state : State a l) :
    IncidenceDirectory.slotCount state = arcCount state := by
  rw [Segment.arc_count_positions]
  change Fintype.card state.Base * 2 ^ l * 2 ^ a = Fintype.card (state.Base × BitWord l) * 2 ^ a
  rw [Fintype.card_prod, Fintype.card_congr (bitWordFinEquiv l), Fintype.card_fin]

/-- The actual online path's transfer writes the terminal tag below the
workspace. Its final memory agrees at every address required by the terminal stage. -/
theorem handoff_of_transfer {m phy : Memory w} {addr value : Word w}
    (post : phy = writeMemory m addr value) (tag : addr.val < (pub 2).val + 6) :
    SourceTransport.Agree ((pub 2).val + 6 ≤ ·) m phy := by
  intro x hx
  rw [post, writeMemory, ite_eq_right (by omega : x ≠ addr.val)]

/-- Read the exact initial and final header operands at the physical terminal
handoff. The suffix agreement allows an outer controller store below the
online workspace control fields. -/
theorem boundary_inputs (m phy : Memory w)
    (boundary : Boundary resident pub (levelWords L : Word w) (directoryRows L)
      (directoryRows L) (vs) (Y) m)
    (handoff : SourceTransport.Agree ((pub 2).val + 6 ≤ ·) m phy)
    (fit : endAddress L < 2 ^ w) (slots : arcCount (Y) ≤ slotCapacity L) :
    Nonempty (SelectedDirectoryHistory.Retained B f hf T hT X z L (endAddress L) phy) ∧
      Ready L (ls).dropLast.length (Aₜ) pub phy ∧
      (packedIncidence L w (ls).dropLast.length (arcCount (Y))).ActualColumns (Y) phy := by
  have size : (L).levels = T * (S.steps + 1) + 1 := by
    rw [BlockProgram.actual_level_count, Nat.mul_comm, Nat.add_comm]
  have wide : 30 ≤ (L).shape.scalarFields := by change 30 ≤ 54; decide
  have idx := selected_last_index B f hf T hT X z
  have nlast := selected_prior_length B f hf T hT X z
  have base : (L).base = (pub 2).val := rfl
  have first : (L).base + 11 + (L).shape.arity ≤ levelStart L 0 := by
    simp only [levelStart, levelsBase, directoryBase, plannerTag, frameBase]
    omega
  have firstFit := (levelStart_mono L (Nat.zero_le (L).levels)).trans_lt fit
  have agree : SourceTransport.Agree (levelStart L 0 ≤ ·) m phy :=
    fun x hx => handoff x (by omega)
  have arcs := slot_count (Y)
  have state := CurrentResident.transfer boundary.stored (by omega) fit (by omega)
    (arcs.le.trans slots) agree
  obtain ⟨⟨⟨history⟩, _⟩, cur, frame⟩ := state
  have hval (i : ℕ) (hi : i ≤ 11 + (L).shape.arity) :
      (pub 2 + (i : Word w)).val = (pub 2).val + i := by
    have small : (pub 2).val + i < 2 ^ w := by omega
    rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : i < 2 ^ w),
      Nat.mod_eq_of_lt small]
  have rows : phy (pub 2 + 8).val = (directoryRows L : Word w) := by
    have val := boundary.totalValue
    change (m (pub 2 + 8).val).val = directoryRows L at val
    have haddr : (pub 2 + 8).val = (pub 2).val + 8 := hval 8 (by omega)
    apply Fin.ext
    rw [← handoff _ (by rw [haddr]; omega), Fin.val_natCast, ← val,
      Nat.mod_eq_of_lt (m _).isLt]
  have pitch : phy (pub 2 + ((10 + (L).shape.arity : ℕ) : Word w)).val =
      (levelWords L : Word w) := by
    have word : (Workspace.ports (Schedule.arity (BlockProgram.script B).catalog) (pub 2)).directory
        - 1 = pub 2 + ((10 + (L).shape.arity : ℕ) : Word w) := by
      change pub 2 + ((11 + (L).shape.arity : ℕ) : Word w) - 1 = _
      rw [show 11 + (L).shape.arity = (10 + (L).shape.arity) + 1 by omega, Nat.cast_add]
      rw [Nat.cast_one, ← add_assoc, add_sub_cancel_right]
    exact (handoff _ (by rw [hval _ (by omega)]; omega)).symm.trans (word ▸ boundary.stride)
  have count : phy (levelStart L 0 + 28) = ((L).levels : Word w) := by
    apply Fin.ext
    rw [Fin.val_natCast, ← cur.startup.levels, Nat.mod_eq_of_lt (phy _).isLt]
  have headCount : IncidenceDirectory.slotCount (Y) = (Y).positions * 2 ^ (S.degreeExponent 0) :=
    arcs.trans (Segment.arc_count_positions (Y))
  refine ⟨⟨history⟩, selected_ready B f hf T hT X z L baseBits laneBits tab rfl pub phy phy
    base.symm rows pitch size wide fit (fun _ _ => rfl) count history ?_ ?_ ?_
    (CursorRAM.encode w (directoryBase L)) (CursorRAM.encode w 1) (S.degreeExponent 0) width
    (incidenceStart L 0) frame, ?_⟩
  · rw [idx]
    exact cur.terminal
  · intro c
    rw [idx, ← headCount]
    exact cur.heads.incidence c
  · rw [idx]
    exact cur.heads.tables tab
  · rw [idx, ← arcs]
    exact cur.incidence.actual

/-- Run the first two actual terminal workers from the selected final
boundary. No separate assumptions on the row pointers, retained cursor
frame, packed graph or header publications are needed. -/
theorem run_boundary (segments : VertexImage.Part → VertexImage.Segment) (r cap : ℕ)
    (m phy : Memory w)
    (boundary : Boundary resident pub (levelWords L : Word w) (directoryRows L)
      (directoryRows L) (vs) (Y) m)
    (handoff : SourceTransport.Agree ((pub 2).val + 6 ≤ ·) m phy)
    (exp : (pub 7).val = r) (hr : r < w) (reserve : 32 ≤ (L).base + 2 ^ r * 2 ^ r)
    (room : (L).base + 2 ^ r * 2 ^ r ≤ 2 ^ w)
    (above : endAddress L ≤ TerminalBootstrap.address (L).base r)
    (slots : arcCount (Y) ≤ slotCapacity L) (cells : arcCount (Y) ≤ tableWords L)
    (totalFit : (Y).totalWidth < 2 ^ w)
    (clock₀ : TerminalBootstrap.cost (L).shape B.recordLimit + 1 + 30 ≤ cap) (clock₁ : 60 ≤ cap) :
    let last := (ls).dropLast.length
    let rawBoot := TerminalBootstrap.report (L).shape B.recordLimit pub 0 phy
    let D := packedIncidence L w last (arcCount (Y))
    let workers := TerminalProgram.workers (L).shape B.recordLimit segments
    Nonempty (SelectedDirectoryHistory.Retained B f hf T hT X z L (endAddress L) phy) ∧
      Ready L last (Aₜ) pub phy ∧
      ∃ rs, Start workers pub cap (TerminalBootstrap.cost (L).shape B.recordLimit + 1) (Y) D
        (tableBase L last tab) phy rawBoot rs ∧
        prefixMemory pub phy rawBoot rs (header pub + 14).val =
          ((words B.recordLimit (ls) + (Y).totalWidth : ℕ) : Word w) := by
  have fit : endAddress L < 2 ^ w := by unfold TerminalBootstrap.address at above; omega
  obtain ⟨history, ready, inc⟩ := boundary_inputs B f hf T hT X z positions baseBits laneBits
    width inputN pub m phy boundary handoff fit slots
  have size : (L).levels = T * (S.steps + 1) + 1 := by
    rw [BlockProgram.actual_level_count, Nat.mul_comm, Nat.add_comm]
  exact ⟨history, ready, run_selected B f hf T hT X z L baseBits laneBits tab segments r cap pub
    phy phy size ready exp hr reserve room above slots cells totalFit (fun _ _ => rfl) inc
    clock₀ clock₁⟩

end PairSimulation.TerminalPrefix.Linked

end VPVNP
end Computability
end OAI
