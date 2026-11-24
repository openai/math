import OAI.Computability.VPVNP.CompressorCompiledResident
import OAI.Computability.VPVNP.PairTerminalPackedPrefix

/-!
# Selected refresh data in the physical DFS memory

The calendar history identifies the producing refresh by its chronological index.
The terminal prefix writes outside its retained cells. Its vertex-entry headers
locate the old graph and the row base used by the child decoder.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.RefreshHookRetained

open BurstRAM Compression Compression.Refresh DescriptorSpace PairSimulation
open LocalHistory TraversalRows TraversalControllerInputs TraversalRoles NodeArguments
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f)
variable {w g : ℕ} (workspace : BurstRAM.Word w) (positions blocks n : ℕ)
variable (X : State S.portExponent (S.portExponent + g))
variable (choice : DyadicRefreshChoice (a₀ := S.degreeExponent 0) (g := g) X S.graph
  (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
local notation "L" => BlockProgram.layout B workspace.val positions blocks
local notation "payload" => CompiledResident.payload B f hf workspace positions blocks n

/-- All physical fields produced for one selected refresh at the given memory. -/
abbrev LevelData (i : ℕ) (m : Memory w) :=
  CompiledResident.RefreshPayload (g := g) B workspace positions blocks n i X choice m

/-- Recover the selected branch's source fields at its occurrence in the calendar. -/
theorem ofPast {past : List (SelectedLevel B f hf)} {m : Memory w}
    (retained : SelectedPayloadHistory.Past B f hf L payload past m) (i : Fin past.length)
    (bits : List Bool) (selected : past[i] =
      RefreshPlacement.selectedLevel (g := g) B f hf X choice bits) :
    LevelData B workspace positions blocks n X choice i.val m := by
  have data := CompiledResident.read (B := B) (f := f) (hf := hf) (workspace := workspace)
    (positions := positions) (blocks := blocks) (n := n) retained i
  apply (CompiledResident.refresh_payload (g := g) B f hf workspace positions blocks n i.val
    X choice bits m).mp
  exact Eq.mp (congrArg (fun v : SelectedLevel B f hf => payload i.val v m) selected) data

variable {lanes : ℕ} (budget : blocks * S.laneBits ≤ lanes)
variable (initial : State (S.degreeExponent 0) lanes)
variable (branch : (B.execute f hf blocks budget initial).Choices)
local notation "levels" => executeLevels B f hf blocks budget initial branch
local notation "tags" => TraversalRoles.selected B f hf blocks budget initial branch
variable {tab : Fin (BlockProgram.layout B workspace.val positions blocks).shape.tables}
variable {baseBits laneBits : ℕ} {pub : Fin 11 → BurstRAM.Word w}
variable {calendar frozen : Memory w}
variable {wireBits : Fin (StateExecution.finalState
  (B.execute f hf blocks budget initial) branch).totalWidth → Bool}
local notation "Vertex" => TerminalProgram.VertexEntry (w := w) (S := S) (n := lanes)
  B f hf blocks budget initial branch L tab baseBits laneBits pub calendar frozen wireBits

/-- The frozen memory after the real bootstrap, final offset scan, traversal rows and
shared bits still contains both incidence directories and every selected term field. -/
theorem atVertex (entry : Vertex)
    (retained : SelectedPayloadHistory.Past B f hf L payload levels calendar)
    (i : Fin (levels).length) (bits : List Bool) (selected : (levels)[i] =
      RefreshPlacement.selectedLevel (g := g) B f hf X choice bits) :
    LevelData B workspace positions blocks n X choice i.val frozen := by
  have live : (selectedLayers B f hf blocks budget initial branch).dropLast.length <
      (L).levels := by
    rw [TerminalBootstrap.selected_prior_length, BlockProgram.actual_level_count,
      Nat.mul_comm blocks]
    omega
  exact ofPast B f hf workspace positions blocks n X choice
    (entry.payload (data := payload) B f hf blocks budget initial branch live retained)
    i bits selected

/-- The row base read at this occurrence is the one computed by the native
traversal. Together with the saved six metadata words it gives the actual child
operand bank at the locator used by the role. -/
theorem childAtVertex (entry : Vertex) (i : Fin (levels).length)
    (data : LevelData B workspace positions blocks n X choice i.val frozen) :
    (ChildScan.directory S.portExponent (layerBase B.recordLimit (endAddress L) tags i.val)
      B.recordLimit ⟨n, frameStride (slotDegree S) n⟩
      (packedIncidence L w i.val (X.positions * 2 ^ S.portExponent))).Stored frozen
      (levelHead pub frozen i.val + 14) := by
  rw [entry.level_head B f hf blocks budget initial branch]
  apply data.child.bank
  obtain ⟨ds, resident⟩ := entry.directories
  have row := resident.currentBase i.val (by
    simpa only [levelFibers, List.length_ofFn] using i.isLt.le)
  rw [levelFibers_tags levels ds] at row
  simpa only [levelStart, Nat.zero_mul, Nat.add_zero, TraversalRoles.selected] using row

end CompressorRecords.RefreshHookRetained

end

end VPVNP
end Computability
end OAI
