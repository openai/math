import OAI.Computability.BorderVNP.RoutingISAExternalBank
import OAI.Computability.BorderVNP.RoutingISACompactWriteLoop
import OAI.Computability.BorderVNP.PackedDirectoryWriter

/-!
# Seeding the sparse cell descriptor from live boundary words

Registers three, four, and five name the source base, bit count, and destination base.
The source index decreases as the output address advances. The ordinary contiguous
store routine uses register twenty as its cursor, so the program saves and restores
the caller's value of that register.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.ExternalSeed

open VPVNP.BurstRAM Packing.Directory.ISA CompactMachine DiagonalResidueRAM

/-- Save the caller's cursor and initialize the bounded scan. -/
def setup : Code := .block [.copy 7 20, .constant 0 0, .constant 1 1, .copy 6 0, .copy 20 5]

/-- Read the next source in reverse address order, check its binary value, and advance the count. -/
def read : Code := .block [.binary .sub 8 4 6, .binary .sub 8 8 1, .binary .add 8 3 8,
  .load 9 8, .ifEq 9 0 .nop (requireEq 9 1), .binary .add 6 6 1]

/-- Source registers of the fixed twelve sparse record digits. -/
def recordRegs : List Reg := [1,0,0,0,0,0,0,0,0,0,9,1]

/-- One checked boundary read followed by its twelve actual RAM writes. -/
def step : Code := .seq read (pushWords recordRegs)

/-- Native seed prefix, ending at the caller's original register twenty. -/
def writer : Code := .seq setup (.seq (.whileLt 6 4 step) (.copy 20 7))

/-- Boundary record prefix after processing the first `i` chronological inputs. -/
def recordPrefix (w : ℕ) (xs : List Bool) (i : ℕ) : List (Word w) :=
  ((xs.reverse.take i).flatMap literalRecord).map (fun b => word w b.toNat)

/-- Each processed bit occupies exactly twelve consecutive word addresses. -/
theorem length_prefix {w : ℕ} (xs : List Bool) {i : ℕ} (hi : i ≤ xs.length) :
    (recordPrefix w xs i).length = 12*i := by
  let ys := xs.reverse.take i
  have h := length_externalRecords ys.reverse
  simpa [recordPrefix, externalRecords, ys, Nat.min_eq_left hi] using h

/-- Advancing the scan appends precisely one literal record for the reverse-addressed bit. -/
theorem prefix_succ {w : ℕ} (xs : List Bool) {i : ℕ} (hi : i < xs.length) :
    recordPrefix w xs (i+1) = recordPrefix w xs i ++
      (literalRecord xs[xs.length-i-1]).map (fun b => word w b.toNat) := by
  have hr : i < xs.reverse.length := by simpa using hi
  simp only [recordPrefix, ← List.take_concat_get' xs.reverse i hr, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append, List.getElem_reverse]
  simp only [show xs.length-1-i = xs.length-i-1 by omega]

/-- The register value assigned to each emitted bit equals the prescribed literal record word. -/
theorem recordRegs_map {w : ℕ} (s : Bank w) (b : Bool) (hz : s 0 = word w 0)
    (ho : s 1 = word w 1) (hb : s 9 = word w b.toNat) :
    recordRegs.map s = (literalRecord b).map (fun v => word w v.toNat) := by
  simp [recordRegs, literalRecord, hz, ho, hb]

end RoutingISA.ExternalSeed

end BorderVNP
end Computability
end OAI
