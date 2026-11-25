import OAI.Computability.BorderVNP.PackedDirectory
import OAI.Computability.BorderVNP.RoutingISANatural

/-! # Fixed team instruction table for the Section 7.3 delivery directory

The output pointer comes from frame word 8. The frame's words 64–70 hold the private and
live placement-table bases, bottom bundle/site count, site count, site block width, padded
description width and presence of the additional pin field. The preceding placement stage
writes two words per table entry, the final cell and the start of the slot range within its bank.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory.ISA

open RoutingISA

/-- Load public layout words and compute the row-major loop dimensions. Register 19
counts candidates, 20 is the next output word, and 21 retains the start of the output. -/
def setup : Code := .block [
  .constant 0 0, .constant 1 1, .constant 2 2,
  readFrame 3 62 63 1, readFrame 4 62 63 2, readFrame 5 62 63 3, readFrame 6 62 63 4,
  readFrame 7 62 63 67, readFrame 8 62 63 68, readFrame 9 62 63 69,
  readFrame 10 62 63 70, .binary .add 10 10 1,
  readFrame 11 62 63 64, readFrame 12 62 63 65, readFrame 13 62 63 66,
  .binary .mul 13 13 2, .binary .div 14 5 8, .binary .add 14 14 2,
  .binary .div 15 5 2, .binary .sub 17 3 1, .binary .mul 17 17 6,
  .binary .mul 16 10 5, .binary .add 16 16 17, .binary .add 17 5 17,
  .binary .mul 18 3 4, .binary .mul 18 18 10, .binary .mul 18 18 14, .binary .add 18 13 18,
  .copy 19 0, readFrame 21 62 63 8, .copy 20 21]

/-- Compute the overlap of one source field and one uniform block. The inputs 22–25
are the source start, source width, block width and candidate block step. The outputs
26, 27, 28 and 38 hold the absolute block number, block start, overlap start and width. -/
def intersection : Code := .block [
  .binary .div 26 22 24, .binary .add 26 26 25, .binary .mul 27 26 24,
  .ifLt 22 27 (.copy 28 27) (.copy 28 22),
  .binary .add 29 22 23, .binary .add 30 27 24,
  .ifLt 30 29 (.copy 29 30) .nop,
  .ifLt 29 28 (.copy 38 0) (.binary .sub 38 29 28)]

/-- Fetch a two-word placement. Register 31 holds the placement index and the
two results are delivered to the cell and destination-start registers 36 and 37. -/
def getPlacement (base : Reg) : Code := .block [
  .binary .mul 39 31 2, .binary .add 39 base 39, .load 36 39,
  .binary .add 39 39 1, .load 37 39]

/-- One private candidate addresses a suffix of a live literal. The first bit delivered
is the overlap start relative to the physical processor tail. -/
def privateCandidate : Code := .block [
  .binary .div 31 19 2, .binary .mod 25 19 2, .binary .mul 22 31 9,
  .copy 23 9, .copy 24 15, intersection,
  .binary .div 32 26 4, .binary .mod 33 26 4, .copy 34 0,
  .binary .sub 35 5 15, .binary .sub 40 28 27, .binary .add 35 35 40,
  getPlacement 11, .binary .sub 40 28 22, .binary .add 37 37 40]

/-- One live-field candidate transports a consecutive range from the actual literal
or pinned-field source to the correct occurrence of the initial site block. -/
def liveCandidate : Code := .block [
  .binary .sub 41 19 13, .binary .div 42 41 14, .binary .mod 25 41 14,
  .binary .div 43 42 10, .binary .div 32 43 4, .binary .mod 33 43 4,
  .binary .mod 34 42 10, .binary .mul 22 33 16, .binary .mul 41 34 17,
  .binary .add 22 22 41, .copy 23 5, .copy 24 8, intersection,
  .binary .sub 35 28 22, .binary .mul 31 32 7, .binary .add 31 31 26,
  getPlacement 12, .binary .sub 40 28 27, .binary .add 37 37 40]

/-- Seven consecutive output words are calculated in registers 32–38. -/
def candidate : Code := .ifLt 19 13 privateCandidate liveCandidate

/-- Store a list of source registers at consecutive word addresses, advancing the cursor
once after every store. The emitted instruction sequence has fixed length. -/
def pushWords : List Reg → Code
  | [] => .nop
  | r :: rs => .seq (.store 20 r) (.seq (.binary .add 20 20 1) (pushWords rs))

/-- Emit a candidate if and only if it contains at least one bit, then advance to the
next candidate. -/
def rowStep : Code := .block [
  candidate, .ifLt 0 38 (pushWords [32,33,34,35,36,37,38]) .nop,
  .binary .add 19 19 1]

/-- Compute the output row count and the address of frame word nine. -/
def finishCalc : Code := .block [.binary .sub 40 20 21,.constant 41 7,.binary .div 40 40 41,
  .publicWord 62 0,.constant 63 9,.binary .add 62 62 63]

/-- Store the populated row count in frame word 9 using the displacement of the
seven-word-aligned output cursor. -/
def finish : Code := .seq finishCalc (.store 62 40)

/-- The complete length-independent assembly fragment generating private, literal and
extra pinned-field demands from the reconstructed placements. -/
def program : Code := .block [setup, .whileLt 19 18 rowStep, finish]

/-- The delivery directory makes no guesses and calls no private subroutine. -/
theorem deterministic : program.deterministic = true := by decide

end Packing.Directory.ISA

end BorderVNP
end Computability
end OAI
