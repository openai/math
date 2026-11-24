import OAI.Computability.VPVNP.PairTerminalPackedPrefix
import OAI.Computability.VPVNP.PairVertexRootFields
import OAI.Computability.VPVNP.PairSimulationPhysicalRootRows

/-!
# The three terminal gather arrays at vertex entry

The final packed incidence bank supplies the inverse and width columns.
The prefix worker fills the disjoint offset array. Header slots 9, 10 and
11 point to these very arrays in the layout read by the root gather.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalProgram

open BurstRAM Compression CompressorRecords DescriptorSpace LocalHistory TraversalRows
open TerminalGatherGeometry TerminalLink
open scoped Fin.CommRing

set_option maxHeartbeats 1600000

variable {w : ℕ}
attribute [local irreducible] BlockSchedule.Templates.execute

open private width_cells from OAI.Computability.VPVNP.PairTerminalPrefix

/-- Recover the gather rows in any handoff memory that retains the final
incidence columns and the freshly computed start offsets. -/
theorem gather_rows_of_columns {a g : ℕ} (Y : State a g) (D : Layout) (last : Fin D.levels)
    (tab : Fin D.shape.tables) (L : TerminalRootGather.Layout) {calendar src : Memory w}
    (incoming : L.incomingHead = incidenceBase D last (TerminalPrefix.arcCount Y) 4)
    (widths : L.widthHead = incidenceBase D last (TerminalPrefix.arcCount Y) 5)
    (starts : L.prefixHead = tableBase D last tab)
    (columns : (packedIncidence D w last (TerminalPrefix.arcCount Y)).ActualColumns Y calendar)
    (fit : endAddress D < 2^w) (slots : TerminalPrefix.arcCount Y ≤ slotCapacity D)
    (totalFit : Y.totalWidth < 2^w)
    (raw : ∀ x < endAddress D, x < tableBase D last tab → src x = calendar x)
    (offsets : ∀ i : Fin (TerminalPrefix.arcCount Y),
      (src (tableBase D last tab+i.val)).val = EndpointBits.offset (TerminalPrefix.width Y) i) :
    Rows Y L src := by
  let count := TerminalPrefix.arcCount Y
  let T := packedIncidence D w last count
  have upto : tableBase D last tab ≤ endAddress D :=
    (Nat.le_add_right ..).trans ((tableEnd_le_nextLevel D last tab).trans (levelStart_mono D last.isLt))
  have bounds (c : Fin 6) (i : Fin count) : incidenceBase D last count c+i.val < tableBase D last tab :=
    (incidence_bounds D last count slots c i).2.trans_le (Nat.le_add_right ..)
  have room := packed_incidence_room D fit last slots
  have hhead (c : Fin 6) : (T.column c).val = incidenceBase D last count c := by
    rw [packed_column]
    apply Nat.mod_eq_of_lt
    have mul := Nat.mul_le_mul_right count c.isLt.le
    change incidenceStart D last + c.val*count < 2^w
    exact (Nat.add_le_add_left mul _).trans_lt room
  have atColumn (c : Fin 6) (i : Fin count) : src (incidenceBase D last count c+i.val) =
      calendar (incidenceBase D last count c+i.val) := raw _ ((bounds c i).trans_le upto) (bounds c i)
  constructor
  · intro e
    let i := number Y e
    let j := number Y (Y.slots.actualGraph.target.symm e)
    have ibound := ((bounds 4 i).trans_le upto).trans fit
    have jbound := ((bounds 4 j).trans_le upto).trans fit
    have hi : i.val < 2^w := (Nat.le_add_left ..).trans_lt ibound
    have hj : j.val < 2^w := (Nat.le_add_left ..).trans_lt jbound
    have loc : (T.actualIn+IncidenceDirectory.actualPort Y e).val = incidenceBase D last count 4+i.val := by
      rw [TerminalPrefix.actualPort_eq, Fin.val_add, show T.actualIn.val = _ from hhead 4]
      change (incidenceBase D last count 4+(i.val%(2^w)))%(2^w) = _
      rw [Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt ibound]
    have col := congrArg Fin.val (columns.actualIn e)
    change (calendar (T.actualIn+IncidenceDirectory.actualPort Y e).val).val = _ at col
    rw [loc] at col
    have target := congrArg Fin.val (TerminalPrefix.actualPort_eq (w := w) Y (Y.slots.actualGraph.target.symm e))
    rw [incoming,atColumn 4 i]
    exact col.trans (target.trans (Nat.mod_eq_of_lt hj))
  · intro i
    have hr : T.width.val + count ≤ 2^w := by
      rw [show T.width.val = _ from hhead 5]
      change incidenceStart D last + 5*count + count ≤ 2^w
      omega
    rw [widths,atColumn 5 i,← show T.width.val = _ from hhead 5]
    exact width_cells Y T calendar columns hr totalFit i
  · intro i
    rw [starts]; exact offsets i

variable {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
variable {B : S.Templates} {f : B.Entry → A} {hf : B.IsSolution f}
variable {n T : ℕ} {hT : T*S.laneBits ≤ n} {X : State (S.degreeExponent 0) n}
variable {z : (B.execute f hf T hT X).Choices}
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z
local notation "last" => List.length (List.dropLast (selectedLayers B f hf T hT X z))
variable {L : Layout} {tab : Fin L.shape.tables} {baseBits laneBits : ℕ} {pub : Fin 11 → Word w}
  {calendar vertex : Memory w} {bits : Fin (StateExecution.finalState (B.execute f hf T hT X) z).totalWidth → Bool}
variable (entry : VertexEntry B f hf T hT X z L tab baseBits laneBits pub calendar vertex bits)
local notation "H" => header pub
local notation "count" => TerminalPrefix.arcCount Y
include entry

/-- The native header loads resolve to the two final incidence columns and
the selected prefix table, uniformly over the current site ordinal. -/
theorem VertexEntry.gather_heads (degree : ℕ) (state : Word w) (hl : last < L.levels)
    (fit : endAddress L < 2^w) (slots : count ≤ slotCapacity L) (headFit : (H).val+12 ≤ 2^w) :
    let G := TerminalRootGather.Layout.ofHeader degree pub H state vertex
    G.incomingHead = incidenceBase L last count 4 ∧
      G.widthHead = incidenceBase L last count 5 ∧ G.prefixHead = tableBase L last tab := by
  let lastFin : Fin L.levels := ⟨last,hl⟩
  have incFit := packed_incidence_room L fit lastFin slots
  have inc (c : Fin 6) : incidenceBase L last count c < 2^w :=
    (Nat.add_le_add_left (Nat.mul_le_mul_right count c.isLt.le) _).trans_lt incFit
  have tableFit : tableBase L last tab < 2^w := (Nat.le_add_right ..).trans_lt
    ((tableEnd_le_nextLevel L last tab).trans_lt (level_room L fit lastFin))
  have addr (j : ℕ) (hj : j < 12) : (H+(j : Word w)).val = (H).val+j := by
    rw [Fin.val_add,Fin.val_natCast,Nat.mod_eq_of_lt (by omega : j < 2^w),Nat.mod_eq_of_lt (by omega)]
  have arcEq := TerminalPrefix.Segment.arc_count_positions Y
  have hi := entry.headers (10 : Fin 21) (by decide) (by decide) (by decide)
  have hw := entry.headers (9 : Fin 21) (by decide) (by decide) (by decide)
  have hs := entry.headers (11 : Fin 21) (by decide) (by decide) (by decide)
  change vertex ((H).val+10) = ((incidenceBase L last _ 4 : ℕ) : Word w) at hi
  change vertex ((H).val+9) = ((incidenceBase L last _ 5 : ℕ) : Word w) at hw
  change vertex ((H).val+11) = ((tableBase L last tab : ℕ) : Word w) at hs
  rw [← arcEq] at hi hw
  change (vertex (H+10).val).val = _ ∧ (vertex (H+9).val).val = _ ∧ (vertex (H+11).val).val = _
  rw [show (H+10).val = _ from addr 10 (by decide),show (H+9).val = _ from addr 9 (by decide),
    show (H+11).val = _ from addr 11 (by decide),hi,hw,hs]
  exact ⟨Nat.mod_eq_of_lt (inc 4),Nat.mod_eq_of_lt (inc 5),Nat.mod_eq_of_lt tableFit⟩

/-- The selected packed calendar supplies the gather rows in the actual
vertex-entry memory, through the header's loaded addresses. -/
theorem VertexEntry.gather_rows (degree : ℕ) (state : Word w) (hl : last < L.levels)
    (fit : endAddress L < 2^w) (slots : count ≤ slotCapacity L) (headFit : (H).val+12 ≤ 2^w)
    (cols : (packedIncidence L w last count).ActualColumns Y calendar) :
    Rows Y (TerminalRootGather.Layout.ofHeader degree pub H state vertex) vertex := by
  obtain ⟨i,b,s⟩ := entry.gather_heads degree state hl fit slots headFit
  exact gather_rows_of_columns Y L ⟨last,hl⟩ tab _ i b s cols fit slots
    (entry.total ▸ (vertex ((H).val+12)).isLt) (fun x hx h => entry.raw x hx (.inl h)) entry.offsets

end PairSimulation.TerminalProgram


namespace PairSimulation.TerminalPrefix.Linked

open BurstRAM Compression CompressorRecords DescriptorSpace TerminalGatherGeometry TerminalLink
open scoped Fin.CommRing

variable {w a g fuel cap : ℕ} {Y : State a g} {workers : Stage → LiveProgram.PairTable}
    {pub : Fin 11 → Word w} {input quiet : Memory w} {boot : Report w} {rs : List (Report w)}
local notation "H" => header pub

/-- The quiet traversal-row builder leaves all three endpoint arrays in place.
This supplies the physical row input before the shared-wire choice is made. -/
theorem Start.quiet_gather_rows (D : Layout) (last : Fin D.levels) (tab : Fin D.shape.tables)
    (degree : ℕ) (state : Word w)
    (s : Start workers pub cap fuel Y (packedIncidence D w last (arcCount Y))
      (tableBase D last tab : Word w) input boot rs)
    (columns : (packedIncidence D w last (arcCount Y)).ActualColumns Y (after input boot.events))
    (keep : ∀ j < endAddress D, quiet j = prefixMemory pub input boot rs j)
    (end_le : endAddress D ≤ (H).val) (room : (H).val+32 ≤ 2^w)
    (slots : arcCount Y ≤ slotCapacity D) (cells : arcCount Y ≤ tableWords D)
    (inverse : (quiet (H+10).val).val = incidenceBase D last (arcCount Y) 4)
    (widths : (quiet (H+9).val).val = incidenceBase D last (arcCount Y) 5)
    (starts : (quiet (H+11).val).val = tableBase D last tab) :
    Rows Y (TerminalRootGather.Layout.ofHeader degree pub H state quiet) quiet := by
  let L := TerminalRootGather.Layout.ofHeader degree pub H state quiet
  have rows := PhysicalScanData.prefix_rows Y L D last tab pub (after input boot.events) rs
    end_le room slots cells inverse widths starts columns s.rawScan
  have bounds := PhysicalScanData.packed_heads D last tab {L with wires := endAddress D} (arcCount Y)
    slots cells inverse widths starts le_rfl
  have saved : (H+31).val = (H).val+31 := by
    change ((H).val+31%(2^w))%(2^w) = _
    rw [Nat.mod_eq_of_lt (by omega : 31 < 2^w),Nat.mod_eq_of_lt (by omega)]
  apply rows.transfer
  intro h hh i
  have bound : h + arcCount Y ≤ endAddress D := bounds h hh
  have hj : h+i.val < endAddress D := (Nat.add_lt_add_left i.isLt _).trans_le bound
  have away : workerCell H (h+i.val) := by unfold workerCell; rw [saved]; omega
  exact (keep _ hj).trans (s.handoff_rows.1 _ away).symm

end PairSimulation.TerminalPrefix.Linked

end VPVNP
end Computability
end OAI
