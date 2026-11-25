import OAI.Computability.BorderVNP.PackedSewnFragmentPairSpec
import OAI.Computability.BorderVNP.ParseBatchRowFrame

/-! # Gate circuit joining two exterior partial translations -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment

open VPVNP.VerifierNetwork ParseBatchSort
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private eqWord from OAI.Computability.BorderVNP.ParseBatchRowFrame

namespace PairGate

/-- Two physical fragment slots. -/
abbrev Raw (w : ℕ) := Bool × Column w

/-- The two slots together with the three sums for the old end, merged width and source end. -/
abbrev Mid (w : ℕ) := Raw w ⊕ (Fin 3 × Fin w)

variable {w : ℕ}

/-- An operand of the address adder. -/
def inputWord (b : Bool) (k : Fin 4) (j : Fin w) : Expr (Raw w) := .input (b,.inr (k,j))

/-- Offset fields advance by the left width. The width field adds the two widths. -/
def sumBit (k : Fin 3) (j : Fin w) : Expr (Raw w) :=
  addWord (inputWord false k.succ) (inputWord (decide (k = 1)) 2) j

/-- Preserve each original pin beside the sums. -/
def loadBit : Mid w → Expr (Raw w)
  | .inl p => .input p
  | .inr (k,j) => sumBit k j

/-- Stage the address sums before comparing their binary values. -/
noncomputable def loaded (w : ℕ) : Frame (Raw w) (Mid w) := (Frame.initial id).step loadBit

/-- A live or source-presence flag on the comparison bus. -/
def flag (b t : Bool) : Expr (Mid w) := .input (.inl (b,.inl t))

/-- One original binary field on the comparison bus. -/
def rawWord (b : Bool) (k : Fin 4) (j : Fin w) : Expr (Mid w) := .input (.inl (b,.inr (k,j)))

/-- An address sum on the comparison bus. -/
def sumWord (k : Fin 3) (j : Fin w) : Expr (Mid w) := .input (.inr (k,j))

/-- Both intervals are clamps, or the right translation starts where the left one ends. -/
def sameSource : Expr (Mid w) :=
  .or (.and (.not (flag false true)) (.not (flag true true)))
    (.and (flag false true) (.and (flag true true) (eqWord (sumWord 2) (rawWord true 3))))

/-- Live adjacent intervals of a single site continuing the same partial translation. -/
def merge : Expr (Mid w) :=
  .and (flag false false) (.and (flag true false)
    (.and (eqWord (rawWord false 0) (rawWord true 0))
      (.and (eqWord (sumWord 0) (rawWord true 1)) sameSource)))

/-- The merged width goes into the left slot and the absorbed right slot is disabled. -/
def outputBit : Raw w → Expr (Mid w)
  | (true,.inl false) => .and (flag true false) (.not merge)
  | (false,.inr (k,j)) =>
    if k = 2 then mux merge (sumWord 1 j) (rawWord false k j) else rawWord false k j
  | p => .input (.inl p)

end PairGate

/-- One physical two-slot coalescing circuit. -/
noncomputable def pair (w : ℕ) : Frame (Bool × Column w) (Bool × Column w) :=
  (PairGate.loaded w).step PairGate.outputBit

end Packing.SewnField.Fragment

end BorderVNP
end Computability
end OAI
