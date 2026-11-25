import OAI.ThreeFlat.RAM.DescriptorExpr

namespace OAI
/-! # Reading trivalent cell words from a compact factor history

A four-word history row contains the three source addresses and the factor
table number. A coefficient is read from a separate table of eight entries.
-/

namespace ThreeFlat.RAM.HistoryFactorScan

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr

variable {w k : ℕ}

/-- The sole input register holds the absolute address of the requested word
in the expanded eleven-word cell layout. A bind puts its result at index zero. -/
def readCellWord (cellsBase metadataBase lutBase : Word w) : Term w k 1 :=
  .bind (.literal cellsBase) <|   -- cellBase
  .bind (.binary .sub 1 0) <|     -- delta
  .bind (.literal 11) <|          -- eleven
  .bind (.binary .div 1 0) <|     -- row
  .bind (.binary .mod 2 1) <|     -- col
  .bind (.literal 4) <|           -- four
  .bind (.binary .mul 0 2) <|     -- rowOffset
  .bind (.literal metadataBase) <|  -- metaBase
  .bind (.binary .add 0 1) <|     -- rowBase
  .bind (.binary .add 0 4) <|     -- sourceAddr
  .bind (.load 0) <|              -- source
  .bind (.literal 3) <|           -- three
  .bind (.binary .add 3 0) <|     -- tagAddr
  .bind (.load 0) <|              -- tag
  .bind (.literal 8) <|           -- eight
  .bind (.binary .mul 0 1) <|     -- tableOffset
  .bind (.literal lutBase) <|     -- lut
  .bind (.binary .add 0 1) <|     -- tableRow
  .bind (.binary .sub 13 6) <|    -- tableCol
  .bind (.binary .add 1 0) <|     -- entryAddr
  .bind (.load 0) <|              -- entry
  .bind (.select .lt 16 9 10 0) <|  -- value
  .result 0

/-- Word-level meaning of the compact reader, including wraparound at the
machine word width. -/
def readWord (cellsBase metadataBase lutBase a : Word w) (m : Memory w) : Word w :=
  let delta := BinaryOp.eval .sub a cellsBase
  let row := BinaryOp.eval .div delta 11
  let col := BinaryOp.eval .mod delta 11
  let rowBase := BinaryOp.eval .add metadataBase (BinaryOp.eval .mul 4 row)
  if col < 3 then m (BinaryOp.eval .add rowBase col).val
  else
    let tag := m (BinaryOp.eval .add rowBase 3).val
    let tableRow := BinaryOp.eval .add lutBase (BinaryOp.eval .mul 8 tag)
    m (BinaryOp.eval .add tableRow (BinaryOp.eval .sub col 3)).val

private theorem word_select (a b yes no : Word w) :
    (if Comparison.lt.test a b then yes else no) = (if a < b then yes else no) := by
  simp [Comparison.test]

set_option maxRecDepth 2048 in
theorem eval_readCellWord (cellsBase metadataBase lutBase : Word w) (data : Fin k → Word w)
    (m : Memory w) (vs : Fin 1 → Word w) :
    (readCellWord cellsBase metadataBase lutBase).eval data m vs =
      readWord cellsBase metadataBase lutBase (vs 0) m := by
  unfold readWord
  exact word_select _ _ _ _

theorem binds_readCellWord (cellsBase metadataBase lutBase : Word w) :
    (readCellWord (k := k) cellsBase metadataBase lutBase).binds = 22 := rfl

end ThreeFlat.RAM.HistoryFactorScan

end OAI
