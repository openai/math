import OAI.Computability.BorderVNP.PackedDirectoryRoom
import OAI.Computability.BorderVNP.TransmissionLegCapacity
import OAI.Computability.BorderVNP.TransmissionImageDirectory
import OAI.Computability.BorderVNP.TransmissionSafeAllocation

/-! # Deterministic physical placement of the routing tables

Reserve the arrays from a chosen base after the full boot frame, input and any earlier
scratch buffers. The public bases depend on the maximum number of rows, so a dynamically
emitted row count changes the loop extent without moving any later array.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

/-- The order of the six native arrays, allowing gaps between them. -/
structure TableLayout.Ordered (l : TableLayout) : Prop where
  /-- All 31 boot fields precede the transmission records. -/
  frame : l.frame + 31 ≤ l.records
  /-- All seven-word records precede the square width table. -/
  records : l.records + 7*l.count ≤ l.widths
  /-- The width table precedes the cubic offset table. -/
  widths : l.widths + l.teams^2 ≤ l.offsets
  /-- The offset table precedes the oriented total table. -/
  offsets : l.offsets + l.teams^3 ≤ l.used
  /-- The oriented total table precedes the ordinal table. -/
  used : l.used + l.teams^2 ≤ l.ordinals

/-- Increasing half-open array intervals give all word-fit and separation
conditions required by the scheduler. -/
theorem TableLayout.Ordered.allocated {l : TableLayout} (ordered : l.Ordered)
    {w : ℕ} (teams : 2 < l.teams) (room : l.ordinals+l.count < 2^w) : l.Allocated w := by
  obtain ⟨frame,records,widths,offsets,used⟩ := ordered
  refine ⟨teams,by omega,?_,?_⟩
  · intro a
    cases a <;> simp only [TableLayout.base,TableLayout.length] <;> omega
  · intro a b i hn ha hb
    cases a <;> cases b <;> simp_all only [TableLayout.contains,TableLayout.base,TableLayout.length,
      ne_eq,not_true_eq_false] <;> omega

/-- Place the six routing arrays in their native order. The row count can be
chosen after the public record capacity and all directory pointers are fixed. -/
def TableLayout.reserve (frame records R maxRows count : ℕ) : TableLayout :=
  let widths := records + 7*maxRows
  let offsets := widths + R^2
  let used := offsets + R^3
  let ordinals := used + R^2
  ⟨frame,R,count,records,widths,offsets,used,ordinals⟩

/-- First address available for later payload or cell-input arrays. -/
def TableLayout.reserveEnd (records R maxRows : ℕ) : ℕ :=
  records + 8*maxRows + 2*R^2 + R^3

/-- Reserving from any base after the boot frame accommodates every emitted row count
up to the prescribed capacity. -/
theorem TableLayout.reserve_ordered {frame records R maxRows count : ℕ} (frameRoom : frame+31 ≤ records)
    (rows : count ≤ maxRows) : (TableLayout.reserve frame records R maxRows count).Ordered := by
  constructor <;> dsimp [TableLayout.reserve] <;> omega

/-- The fixed allocation's upper sentinel bounds the live ordinal array. -/
theorem TableLayout.reserve_extent {frame records R maxRows count : ℕ} (rows : count ≤ maxRows) :
    let l := TableLayout.reserve frame records R maxRows count
    l.ordinals+l.count ≤ TableLayout.reserveEnd records R maxRows := by
  dsimp [TableLayout.reserve,TableLayout.reserveEnd]
  omega

/-- A single fitted upper sentinel supplies every required address bound for the
concrete scheduler allocation. -/
theorem TableLayout.reserve_allocated {w frame records R maxRows count : ℕ} (teams : 2 < R)
    (frameRoom : frame+31 ≤ records) (rows : count ≤ maxRows)
    (room : TableLayout.reserveEnd records R maxRows < 2^w) :
    (TableLayout.reserve frame records R maxRows count).Allocated w :=
  (TableLayout.reserve_ordered frameRoom rows).allocated teams
    ((TableLayout.reserve_extent rows).trans_lt room)

/-- The same quartic word range used by the packed-directory writer covers this
allocation's final sentinel when the base, team count and record capacity fit the
public bound. -/
theorem TableLayout.reserveEnd_le_wordBound {records R maxRows B : ℕ}
    (base : records ≤ B) (teams : R ≤ B) (rows : maxRows ≤ B) :
    TableLayout.reserveEnd records R maxRows ≤ Packing.Directory.ISA.wordBound B := by
  calc
    _ ≤ B + 8*B + 2*B^2 + B^3 := by unfold TableLayout.reserveEnd; gcongr
    _ ≤ _ := by unfold Packing.Directory.ISA.wordBound; nlinarith [Nat.zero_le (B^4), Nat.zero_le (B^3)]

/-- All earlier memory, including any extended frame fields before the chosen record
base, survives construction of the scheduling tables. -/
theorem TableLayout.Image.before_records {l : TableLayout} {row : ℕ → TableRow} {before mem : ℕ → ℕ}
    (image : l.Image row before mem) (ordered : l.Ordered) {a : ℕ} (ha : a < l.records) :
    mem a = before a := by
  obtain ⟨_,rec,widths,off,used⟩ := ordered
  apply image.outside <;> simp only [TableLayout.contains,TableLayout.base,TableLayout.length] <;> omega

/-- The physical processor layout in the boot frame, including the header destination
in field 25, remains available in the post-scheduler memory. -/
theorem TableLayout.Image.broadcast_of_ordered {l : TableLayout} {row : ℕ → TableRow} {before mem : ℕ → ℕ}
    (image : l.Image row before mem) (ordered : l.Ordered) {pub : Arg → ℕ} (hf : pub 0 = l.frame)
    {f : BroadcastFrame} (initial : f.At pub before) : f.At pub mem := by
  have eq (i : ℕ) (hi : i < 31) : frameField pub mem i = frameField pub before i := by
    unfold frameField
    apply image.before_records ordered
    have := ordered.frame
    omega
  simpa only [BroadcastFrame.At, eq 0 (by decide), eq 1 (by decide), eq 2 (by decide), eq 3 (by decide),
    eq 4 (by decide), eq 5 (by decide), eq 25 (by decide)] using initial

/-- A row's destinations after the scheduling allocation are disjoint from the
physical descriptor and ordinal arrays at every intervening write. -/
theorem Transmission.Range.directorySeparated_of_ordered {w : ℕ} {l : TableLayout} (ordered : l.Ordered)
    (r : Transmission.Range w) (self : Word w)
    (dest : ∀ mode, r.selected self = some (some mode) → ∀ d ∈ mode.destinations,
      l.ordinals+l.count ≤ (r.bank self d).val ∧ (r.bank self d).val+r.width.val ≤ 2^w) :
    r.directorySeparated self l := by
  obtain ⟨_,rec,widths,off,used⟩ := ordered
  intro mode sel d hd
  obtain ⟨after,room⟩ := dest mode sel d hd
  refine ⟨room,fun a ha => Or.inl ?_⟩
  rcases ha with h | h <;> simp only [TableLayout.contains,TableLayout.base,TableLayout.length] at h <;> omega

/-- Placing destinations after the ordinal table separates them from the entire schedule:
the physical frame, all cubic offsets and both orientations of the totals. -/
theorem Transmission.Range.scheduleSeparated_of_ordered {w : ℕ} {l : TableLayout}
    {row : ℕ → TableRow} {before : ℕ → ℕ} {m : Memory w}
    (image : l.Image row before (readings m)) (ordered : l.Ordered)
    (pub : Arg → Word w) (hf : (pub 0).val = l.frame) (loaded : l.frameFields before)
    (r : Transmission.Range w) (self : Word w)
    (dest : ∀ mode, r.selected self = some (some mode) → ∀ d ∈ mode.destinations,
      l.ordinals+l.count ≤ (r.bank self d).val ∧ (r.bank self d).val+r.width.val ≤ 2^w) :
    r.scheduleSeparated self pub m l.teams := by
  have field (i : ℕ) (hi : i < 31) : frameField (readings pub) (readings m) i = before (l.frame+i) := by
    change readings m ((pub 0).val+i) = before (l.frame+i)
    rw [hf]
    exact image.before_records ordered (by have := ordered.frame; omega)
  apply r.scheduleSeparated_of_above
  intro mode sel d hd
  obtain ⟨after,room⟩ := dest mode sel d hd
  refine ⟨le_trans ?_ after,room⟩
  rw [Transmission.scheduleCeiling,field 17 (by decide),field 18 (by decide),
    loaded.2.2.2.2.1,loaded.2.2.2.2.2.1]
  change max ((pub 0).val+26) (max (l.offsets+l.teams^3) (l.used+l.teams^2)) ≤ l.ordinals+l.count
  obtain ⟨frame,rec,widths,off,used⟩ := ordered
  omega

end RoutingISA

end BorderVNP
end Computability
end OAI
