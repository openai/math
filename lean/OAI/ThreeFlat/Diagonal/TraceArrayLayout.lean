import OAI.ThreeFlat.Diagonal.TraceCircuitArray
import OAI.ThreeFlat.Diagonal.LaneCursorLayout

namespace OAI
/-! # Physical comparison-row addresses for assembled trivalent verifiers -/

namespace ThreeFlat.Diagonal.TraceCircuit

open LaneCursor
variable {F : Type*} {n p q b c k low o : ℕ}

private abbrev rowCount (k low : ℕ) := 2^k * 2^low

/-- Hidden gate bits reside in their owner's row, after the shared register
and sorting inputs at the front of the hidden array. -/
def blockHiddenRow (shared : Fin b → Row k low) : Fin (b+rowCount k low*n) → Row k low :=
  Fin.addCases shared (fun u => (finProdFinEquiv.symm u : Row k low × Fin n).1)

private theorem local_source (v : Row k low) (inputs : Row k low → Fin q → BitSource b p)
    (shared : Fin b → Row k low) (pin : Fin p → Row k low) (z : BitSource n q) :
    sourceRow (blockHiddenRow shared) pin v (rowAddress v inputs z) =
      match z with
      | .pin j => sourceRow shared pin v (inputs v j)
      | _ => v := by
  cases z with
  | constant => rfl
  | hidden h =>
    simp only [rowAddress, sourceRow, blockHiddenRow, Fin.addCases_right]
    exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (v,h))
  | pin j => cases he : inputs v j <;> simp [rowAddress, sourceRow, blockHiddenRow, he]

private def local_code (code : Fin q → Fin o) (zero : Fin o) : BitSource n q → Fin o
  | .pin j => code j
  | _ => zero

private theorem local_reach (v : Row k low) (inputs : Row k low → Fin q → BitSource b p)
    (shared : Fin b → Row k low) (pin : Fin p → Row k low) (offset : Fin o → Row k low)
    (zero : Fin o) (hz : (offset zero).val = 0) (code : Fin q → Fin o)
    (h : ∀ j, v = partner (sourceRow shared pin v (inputs v j)) (offset (code j))) (s : BitSource n q) :
    v = partner (sourceRow (blockHiddenRow shared) pin v (rowAddress v inputs s)) (offset (local_code code zero s)) := by
  rw [local_source]
  cases s with
  | pin j => exact h j
  | hidden | constant => apply Fin.ext; simp [partner,local_code,hz]

/-- Turn a public XOR itinerary for local row operands into the precise
row-layout input of the cursor contraction. Private gates add only the
zero displacement. A cell's in-row ordinal is exactly its block offset. -/
def arrayLayout (rows : Row k low → Fin c → Cell F n q)
    (inputs : Row k low → Fin q → BitSource b p) (shared : Fin b → Row k low)
    (pin : Fin p → Row k low) (offset : Fin o → Row k low) (zeroIndex : Fin o)
    (localZero : (offset zeroIndex).val = 0)
    (code : Row k low → Fin q → Fin o)
    (reaches : ∀ v j, v = partner (sourceRow shared pin v (inputs v j)) (offset (code v j))) :
    RowLayout (assemble rows inputs) k low o c where
  cellAddress := finProdFinEquiv.symm.toEmbedding
  hiddenRow := blockHiddenRow shared
  pinRow := pin
  offset := offset
  code e := let ij : Row k low × Fin c := finProdFinEquiv.symm e.val.1
            local_code (code ij.1) zeroIndex ((rows ij.1 ij.2).source e.val.2)
  reaches e := by
    let ij : Row k low × Fin c := finProdFinEquiv.symm e.val.1
    exact local_reach ij.1 inputs shared pin offset zeroIndex localZero (code ij.1)
      (reaches ij.1) ((rows ij.1 ij.2).source e.val.2)

end ThreeFlat.Diagonal.TraceCircuit

end OAI
