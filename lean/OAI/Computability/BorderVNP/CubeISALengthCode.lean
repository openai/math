import OAI.Computability.BorderVNP.RoutingISACheckLoop
import OAI.Computability.BorderVNP.RoutingISAChecked
import OAI.Computability.BorderVNP.RoutingISAAddressProof
import OAI.Computability.BorderVNP.CubeFirstMinimum

/-! # Native row and coordinate checks for cube length declarations

Frame word 63 points to six secondary words, in order: the computed and declared
row-array bases, the number of entries, the column-total base, the number of
coordinates, and the declared coordinate. The two read-only scans use registers
56 through 63. All arithmetic is unsigned word arithmetic.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeLengths

open VPVNP.BurstRAM

/-- Layout read from the six words of the secondary header. -/
structure Layout where
  /-- Base of the row entries recomputed from the selectors. -/
  actual : ℕ
  /-- Base of the claimed row entries. -/
  claimed : ℕ
  /-- Number of row entries compared by this team. -/
  entries : ℕ
  /-- Base of the directional width totals. -/
  totals : ℕ
  /-- Number of coordinate directions. -/
  coordinates : ℕ
  /-- Raw decoded coordinate claim, prior to checking its range. -/
  chosen : ℕ

/-- Read the secondary header through the addressed primary frame. -/
def layout (pub : Arg → ℕ) (mem : ℕ → ℕ) : Layout :=
  let h := frameField pub mem 63
  ⟨mem (h+0), mem (h+1), mem (h+2), mem (h+3), mem (h+4), mem (h+5)⟩

/-- All physical header and array addresses used by the two scans fit the word width. -/
structure Fits (w : ℕ) (pub : Arg → ℕ) (mem : ℕ → ℕ) : Prop where
  /-- Address of the primary pointer. -/
  primary : pub 0 + 63 < 2^w
  /-- Address of the last secondary word. -/
  header : frameField pub mem 63 + 5 < 2^w
  /-- Exclusive end of the computed row array. -/
  actual : (layout pub mem).actual + (layout pub mem).entries ≤ 2^w
  /-- Exclusive end of the declaration array. -/
  claimed : (layout pub mem).claimed + (layout pub mem).entries ≤ 2^w
  /-- Exclusive end of the column array. -/
  totals : (layout pub mem).totals + (layout pub mem).coordinates ≤ 2^w

/-- Read a secondary header field. The two scratch registers carry real addresses. -/
def field (dst : Reg) (offset : Word 8) : Code := .block [
  readFrame 62 62 63 63, .constant 63 offset, .binary .add 62 62 63, .load dst 62]

/-- Registers loaded at the start of the row-equality scan. -/
def rowSetup : Code := .block [field 58 0, field 59 1, field 57 2,
  .constant 56 0, .constant 60 1, .constant 61 0]

/-- Compare the two addressed entries and advance one position. -/
def rowBody : Code := .block [
  .binary .add 62 58 56, .load 62 62, .binary .add 63 59 56, .load 63 63,
  requireEq 62 63, .binary .add 56 56 60]

/-- Reject any difference in the computed and declared contiguous row entries. -/
def rows : Code := .seq rowSetup (.whileLt 56 57 rowBody)

/-- Read the base of the totals, the number of coordinates and the raw coordinate claim. -/
def minSetup : Code := .block [field 58 3, field 57 4, field 59 5,
  .constant 56 0, .constant 60 1, .constant 61 0]

/-- Load the candidate's width once after the range check. -/
def pivot : Code := .block [.binary .add 62 58 59, .load 61 62]

/-- The comparison at one coordinate, using a strict test only before the claimed index. -/
def minGuard : Code := .ifLt 56 59 (requireLt 61 62) (.ifLt 62 61 .reject .nop)

/-- Test strict minimality against all earlier indices and weak minimality against
the declared coordinate and later indices. -/
def minBody : Code := .block [
  .binary .add 62 58 56, .load 62 62,
  minGuard, .binary .add 56 56 60]

/-- Native coordinate verifier. An out-of-range claim rejects before the pivot load. -/
def minimum : Code := .seq minSetup
  (.ifLt 59 57 (.seq pivot (.whileLt 56 57 minBody)) .reject)

/-- Full row and coordinate test. Neither scan writes to memory. -/
def check : Code := .seq rows minimum

/-- The computed and declared row entries agree at every addressed position. -/
def RowsAgree (l : Layout) (mem : ℕ → ℕ) : Prop :=
  ∀ i < l.entries, mem (l.actual+i) = mem (l.claimed+i)

/-- The claim is in range and the width at every earlier position is strictly larger. -/
def Least (l : Layout) (mem : ℕ → ℕ) : Prop :=
  l.chosen < l.coordinates ∧ ∀ j < l.coordinates,
    if j < l.chosen then mem (l.totals+l.chosen) < mem (l.totals+j)
    else mem (l.totals+l.chosen) ≤ mem (l.totals+j)

/-- The native comparison rule picks precisely the manuscript's first minimizer. -/
theorem least_iff_first {n : ℕ} (l : Layout) (mem : ℕ → ℕ)
    (size : l.coordinates = n+1) :
    Least l mem ↔ l.chosen = (Cube.firstMinimum (fun i : Fin (n+1) => mem (l.totals+i.val))).val := by
  let widths (i : Fin (n+1)) := mem (l.totals+i.val)
  constructor
  · rintro ⟨valid,checkWidth⟩
    let i : Fin (n+1) := ⟨l.chosen, size ▸ valid⟩
    have he : Cube.firstMinimum widths = i := (Cube.firstMinimum_eq_iff_scan widths i).mpr
      ⟨fun j hj => by simpa [widths,i,show j.val < l.chosen from hj] using checkWidth j (by rw [size]; exact j.isLt),
       fun j hj => by simpa [widths,i,show ¬ j.val < l.chosen from hj.not_gt] using checkWidth j (by rw [size]; exact j.isLt)⟩
    exact (congrArg Fin.val he).symm
  · intro he
    let i := Cube.firstMinimum widths
    have hi : l.chosen = i.val := he
    refine ⟨by rw [size,hi]; exact i.isLt, ?_⟩
    intro j hj
    let k : Fin (n+1) := ⟨j,size ▸ hj⟩
    obtain ⟨le,first⟩ := (Cube.firstMinimum_eq_iff widths i).mp rfl
    rw [hi]
    split
    · exact lt_of_not_ge fun bad => (show k < i from ‹j < i.val›).not_ge (first k bad)
    · exact le k

/-- Caller-visible data preserved by both scans. -/
def Kept (regs : Reg → ℕ) (mem : ℕ → ℕ) (z : NatState) : Prop :=
  z.mem = mem ∧ ∀ i : Reg, i.val < 56 → z.reg i = regs i

end RoutingISA.CubeLengths

end BorderVNP
end Computability
end OAI
