import OAI.Computability.BorderVNP.RoutingISATableState
import OAI.Computability.BorderVNP.RoutingISATableBounds

/-! # Native placement of private descriptions after supplied cell inputs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.PrivatePlacement

open VPVNP.BurstRAM

/-- Geometry and public dimensions read at the start of the placement pass. -/
structure Layout where
  /-- Start of the public frame. -/
  frame : ℕ
  /-- The two-word placement table for original sites. -/
  raw : ℕ
  /-- Number of original sites. -/
  entries : ℕ
  /-- Padded description width. -/
  desc : ℕ
  /-- Number of final cells. -/
  cells : ℕ
  /-- Number of physical cables. -/
  cables : ℕ
  /-- Base of the two incidence words per cable. -/
  incidence : ℕ
  /-- Reserved address capacity for the checked report tail following supplied words. -/
  gap : ℕ

/-- Supplied counts follow the two incidence entries of each physical cable. -/
def Layout.supplied (l : Layout) := l.incidence+2*l.cables

/-- Zero-initialized running counts immediately follow the supplied counts. -/
def Layout.scratch (l : Layout) := l.supplied+l.cells

/-- Original cell destination in the first word of a placement record. -/
def Layout.owner (l : Layout) (before : ℕ → ℕ) (i : ℕ) := before (l.raw+2*i)

/-- Total private description width in earlier records assigned to cell `c`. -/
def prefixCounts (owner : ℕ → ℕ) (desc i c : ℕ) : ℕ :=
  ∑ j ∈ Finset.range i, if owner j = c then desc else 0

/-- Read public configuration, calculate the two count-array pointers, and clear the row index. -/
def setup : Code := .block [
  .constant 1 1, .constant 2 2, readFrame 3 62 63 64, readFrame 4 62 63 66,
  readFrame 5 62 63 69, readFrame 6 62 63 87, readFrame 7 62 63 11,
  readFrame 8 62 63 7, .binary .mul 8 2 8, .binary .add 6 6 8,
  .binary .add 7 6 7, readFrame 9 62 63 92, .constant 8 8, .binary .add 9 9 8,
  .load 9 9, .constant 10 0]

/-- Read the original cell, write its new private slot, and add one description
width to that cell's running count. -/
def step : Code := .block [
  .binary .mul 11 2 10, .binary .add 11 3 11, .load 12 11, .binary .add 11 11 1,
  .binary .add 13 6 12, .load 14 13, .binary .add 15 7 12, .load 16 15,
  .binary .add 17 14 9, .binary .add 17 17 16, .store 11 17, .binary .add 16 16 5, .store 15 16,
  .binary .add 10 10 1]

/-- The pass traverses the original sites exactly once. -/
def program : Code := .seq setup (.whileLt 10 4 step)

end RoutingISA.PrivatePlacement

end BorderVNP
end Computability
end OAI
