import OAI.Computability.VPVNP.CompressorSelectedDirectoryHistory
import OAI.Computability.VPVNP.PairTerminalSelectedHeaders
import OAI.Computability.VPVNP.PairTerminalPrefixLinked
import OAI.Computability.VPVNP.PairTerminalPrefixBudget
import OAI.Computability.VPVNP.PairSimulationTerminalProgram

/-!
# Entering the terminal program after a selected compression schedule

The final level is indexed by the number of executed elementary passes. Its
published scalar 14 counts exactly the traversal rows before the final layer.
Agreement on the level - data suffix carries the selected headers and final
incidence columns from the raw calendar walk to its physical output memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalBootstrap

open BurstRAM PrivateRAM Compression CompressorRecords DescriptorSpace
open TraversalRows TraversalRoles LocalHistory
open scoped Fin.CommRing

variable {w : ℕ} {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f) {n : ℕ}
variable (T : ℕ) (hT : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
variable (z : (B.execute f hf T hT X).Choices)
local notation "ls" => selectedLayers B f hf T hT X z
local notation "vs" => executeLevels B f hf T hT X z
local notation "tags" => TraversalRoles.selected B f hf T hT X z
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z

/-- The last level index agrees with the retained directory history, including
when there are no compression blocks. -/
theorem selected_last_index : (ls).dropLast.length = (vs).length := by
  simp only [← selected_layers B f hf T hT X z, selected, List.length_dropLast, List.length_map,
    List.length_cons, Nat.add_sub_cancel]

theorem selected_last_base (base : ℕ) : layerBase B.recordLimit base (tags) (ls).dropLast.length =
    base + words B.recordLimit (ls).dropLast := by
  rw [layerBase, List.map_take, selected_layers B f hf T hT X z, List.length_dropLast,
    List.dropLast_eq_take]

/-- Reconstruct the bootstrap operands in the physical online output memory
from the final raw scalar and pointer publications and the retained row - base
fields. The row - count and pitch control words come from the online run. -/
theorem selected_ready (L : Layout) (baseBits laneBits : ℕ) (tab : Fin L.shape.tables)
    (zero : tab.val = 0) (pub : Fin 11 → Word w) (raw phy : Memory w)
    (workspace : (pub 2).val = L.base) (rows : phy (pub 2 + 8).val = (directoryRows L : Word w))
    (pitch : phy (pub 2 + ((10 + L.shape.arity : ℕ) : Word w)).val = (levelWords L : Word w))
    (size : L.levels = T * (S.steps + 1) + 1) (wide : 30 ≤ L.shape.scalarFields)
    (fit : endAddress L < 2 ^ w)
    (agree : SourceTransport.Agree (levelStart L 0 ≤ ·) raw phy)
    (levelCount : raw (levelStart L 0 + 28) = (L.levels : Word w))
    (history : SelectedDirectoryHistory.Retained B f hf T hT X z L (endAddress L) raw)
    (current : Scalars.Present (.terminal (S.degreeExponent 0)) (Fintype.card (Y).Base)
      (n - T * S.laneBits) (levelStart L (ls).dropLast.length : Word w) raw)
    (columns : ∀ c : Fin 6, raw (incidenceHead L (ls).dropLast.length c) =
      (incidenceBase L (ls).dropLast.length ((Y).positions * 2 ^ (S.degreeExponent 0)) c : Word w))
    (table : raw (tableHead L (ls).dropLast.length tab) =
      (tableBase L (ls).dropLast.length tab : Word w))
    (p q : Word w) (degree width firstColumn : ℕ)
    (saved : Frame.data ((levelStart L 0 : Word w) + 6) raw =
      CursorRAM.ScheduleInit.inputs p q baseBits laneBits degree width firstColumn) :
    Ready L (ls).dropLast.length
      (fromState L (ls).dropLast B.recordLimit baseBits laneBits (Y) tab) pub phy := by
  let last := (ls).dropLast.length
  have heads (j : ℕ) (hj : j ≤ (vs).length) : raw (levelStart L j + 14) =
      (layerBase B.recordLimit (endAddress L) (tags) j : Word w) := history.current j hj
  have size' : L.levels = last + 1 :=
    size.trans (congrArg (· + 1) (selected_prior_length B f hf T hT X z).symm)
  have bound (i j : ℕ) (hi : i < L.levels) (hj : j < levelWords L) : levelStart L i + j < 2 ^ w :=
    (show levelStart L i + j < levelStart L (i + 1) by simp [levelStart, Nat.succ_mul]; omega).trans
      (level_room L fit ⟨i, hi⟩)
  have below (i j : ℕ) : levelStart L 0 ≤ levelStart L i + j :=
    (levelStart_mono L (Nat.zero_le i)).trans (Nat.le_add_right ..)
  have cell (i j : ℕ) (hi : i < L.levels) (hj : j < levelWords L) :
      phy ((levelStart L i : Word w) + (j : Word w)).val =
        raw ((levelStart L i : Word w) + (j : Word w)).val := by
    rw [← Nat.cast_add, Fin.val_natCast, Nat.mod_eq_of_lt (bound i j hi hj)]
    exact (agree _ (below i j)).symm
  have span : L.shape.scalarFields ≤ levelWords L := by
    simp only [levelWords, levelHeaderWords]; omega
  refine ready_of_published L (ls).dropLast B.recordLimit baseBits laneBits (Y) tab zero pub phy
    workspace rows pitch size' wide fit ?_ ?_ ?_ ?_ ?_ ?_ p q degree width firstColumn ?_
  · exact (agree _ (below 0 28)).symm.trans levelCount
  · rw [← agree _ (below 0 14), heads 0 (Nat.zero_le _), layerBase_zero]
  · rw [← agree _ (below last 14), heads _ (selected_last_index B f hf T hT X z).le,
      selected_last_base B f hf T hT X z]
  · intro j
    change (phy ((levelStart L last : Word w) + (j.val : Word w)).val).val = _
    rw [cell last j.val (by omega) (by have := j.isLt; omega)]
    exact current j
  · intro c
    have lo : levelStart L 0 ≤ incidenceHead L last c := by
      simpa only [incidenceHead, Nat.add_assoc] using below last (L.shape.scalarFields + c.val)
    exact (agree _ lo).symm.trans (columns c)
  · have lo : levelStart L 0 ≤ tableHead L last tab := by
      simpa only [tableHead, Nat.add_assoc] using below last (L.shape.scalarFields + 6 + tab.val)
    exact (agree _ lo).symm.trans table
  · funext j
    have mem : phy (((levelStart L 0 : Word w) + 6) + (j.val : Word w)).val =
        raw (((levelStart L 0 : Word w) + 6) + (j.val : Word w)).val := by
      simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc] using
        cell 0 (6 + j.val) (by omega) (by have := j.isLt; omega)
    exact mem.trans (congrFun saved j)

end PairSimulation.TerminalBootstrap

namespace PairSimulation.TerminalPrefix.Linked

open BurstRAM PrivateRAM Compression CompressorRecords DescriptorSpace LocalHistory TraversalRows
open TerminalBootstrap TerminalLink
open scoped Fin.CommRing

variable {w : ℕ}

/-- Transfer the actual edge columns along the same level-data agreement as the
header publications. Each address is in the packed suffix, even for parallel
arcs and fixed loops. -/
theorem packed_actual_online {a g : ℕ} (L : Layout) (last : Fin L.levels) (Y : State a g)
    (slots : arcCount Y ≤ slotCapacity L) (fit : endAddress L < 2 ^ w) (raw phy : Memory w)
    (agree : SourceTransport.Agree (levelStart L 0 ≤ ·) raw phy)
    (old : (packedIncidence L w last (arcCount Y)).ActualColumns Y raw) :
    (packedIncidence L w last (arcCount Y)).ActualColumns Y phy := by
  let T := packedIncidence L w last (arcCount Y)
  have low (c : Fin 6) (e : Y.network.Edge) :
      levelStart L 0 ≤ (T.column c + IncidenceDirectory.actualPort Y e).val := by
    let i := (edgeOrder Y).entries.symm e
    have bounds := incidence_bounds L last (arcCount Y) slots c i
    have top := packed_incidence_room L fit last slots
    have small : incidenceBase L last (arcCount Y) c + i.val < 2 ^ w := by
      have h := Nat.mul_le_mul_right (arcCount Y) c.isLt
      rw [Nat.succ_mul] at h
      have hi : i.val < arcCount Y := i.isLt
      unfold incidenceBase
      omega
    rw [packed_column, actualPort_eq]
    change levelStart L 0 ≤
      (incidenceBase L last (arcCount Y) c % (2 ^ w) + i.val % (2 ^ w)) % (2 ^ w)
    rw [Nat.mod_eq_of_lt (by omega : incidenceBase L last (arcCount Y) c < 2 ^ w),
      Nat.mod_eq_of_lt (by omega : i.val < 2 ^ w), Nat.mod_eq_of_lt small]
    exact (levelStart_mono L (Nat.zero_le last.val)).trans
      ((Nat.le_add_right .. : levelStart L last ≤ incidenceStart L last).trans bounds.1)
  exact ⟨fun e => (agree _ (low 3 e)).symm.trans (old.actualOut e),
    fun e => (agree _ (low 4 e)).symm.trans (old.actualIn e),
    fun e => (agree _ (low 5 e)).symm.trans (old.width e)⟩

variable {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f) {n : ℕ}
variable (T : ℕ) (hT : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
variable (z : (B.execute f hf T hT X).Choices)
local notation "ls" => selectedLayers B f hf T hT X z
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z

/-- The actual five-stage terminal table, started in the post-calendar physical
memory, builds every offset and the role displacement for this selected branch. -/
theorem run_selected (L : Layout) (baseBits laneBits : ℕ) (tab : Fin L.shape.tables)
    (segments : VertexImage.Part → VertexImage.Segment) (r cap : ℕ)
    (pub : Fin 11 → Word w) (raw phy : Memory w) (size : L.levels = T * (S.steps + 1) + 1)
    (ready : Ready L (ls).dropLast.length
      (fromState L (ls).dropLast B.recordLimit baseBits laneBits (Y) tab) pub phy)
    (exp : (pub 7).val = r) (hr : r < w) (reserve : 32 ≤ L.base + 2 ^ r * 2 ^ r)
    (room : L.base + 2 ^ r * 2 ^ r ≤ 2 ^ w)
    (above : endAddress L ≤ TerminalBootstrap.address L.base r)
    (slots : arcCount (Y) ≤ slotCapacity L) (cells : arcCount (Y) ≤ tableWords L)
    (totalFit : (Y).totalWidth < 2 ^ w)
    (agree : SourceTransport.Agree (levelStart L 0 ≤ ·) raw phy)
    (old : (packedIncidence L w (ls).dropLast.length (arcCount (Y))).ActualColumns (Y) raw)
    (clock₀ : TerminalBootstrap.cost L.shape B.recordLimit + 1 + 30 ≤ cap) (clock₁ : 60 ≤ cap) :
    let last := (ls).dropLast.length
    let rawBoot := TerminalBootstrap.report L.shape B.recordLimit pub 0 phy
    let D := packedIncidence L w last (arcCount (Y))
    let workers := TerminalProgram.workers L.shape B.recordLimit segments
    ∃ rs, Start workers pub cap (TerminalBootstrap.cost L.shape B.recordLimit + 1) (Y) D
        (tableBase L last tab) phy rawBoot rs ∧
      prefixMemory pub phy rawBoot rs (header pub + 14).val =
        ((words B.recordLimit (ls) + (Y).totalWidth : ℕ) : Word w) := by
  have len := selected_prior_length B f hf T hT X z
  let last : Fin L.levels := ⟨(ls).dropLast.length, by omega⟩
  let A := fromState L (ls).dropLast B.recordLimit baseBits laneBits (Y) tab
  have fit : endAddress L < 2 ^ w := by unfold TerminalBootstrap.address at above; omega
  have arcs := Segment.arc_count_positions (Y)
  have sites : A.sites * A.degree = arcCount (Y) := by
    rw [show A.sites = (Y).positions from fromState_sites .., arcs]
    rfl
  have wh : A.widthHead = incidenceBase L last (arcCount (Y)) 5 := by rw [arcs]; rfl
  obtain ⟨rs, start, role⟩ := run_packed (TerminalProgram.workers L.shape B.recordLimit segments)
    L last tab A B.recordLimit r cap rfl rfl pub phy (Y) ready exp hr reserve room above
    sites wh rfl slots cells totalFit (packed_actual_online L last (Y) slots fit raw phy agree old)
    clock₀ clock₁
  have hv := header_val L pub r ready.workspace exp hr reserve room
  have fitH : (header pub).val + 32 ≤ 2 ^ w := by rw [hv, TerminalBootstrap.address]; omega
  have H14 : (header pub + 14).val = (header pub).val + 14 := by
    change ((header pub).val + 14 % (2 ^ w)) % (2 ^ w) = _
    rw [Nat.mod_eq_of_lt (by omega : 14 < 2 ^ w), Nat.mod_eq_of_lt (by omega)]
  have H31 : (header pub + 31).val = (header pub).val + 31 := by
    change ((header pub).val + 31 % (2 ^ w)) % (2 ^ w) = _
    rw [Nat.mod_eq_of_lt (by omega : 31 < 2 ^ w), Nat.mod_eq_of_lt (by omega)]
  have cell : workerCell (header pub) (header pub + 14).val := by
    unfold workerCell
    rw [H14, H31]
    omega
  refine ⟨rs, start, (start.handoff_rows.1 _ cell).symm.trans ?_⟩
  exact role.trans (congrArg (fun d : ℕ => ((d + (Y).totalWidth : ℕ) : Word w))
    (selected_rowWords B f hf T hT X z L baseBits laneBits tab))

end PairSimulation.TerminalPrefix.Linked

end VPVNP
end Computability
end OAI
