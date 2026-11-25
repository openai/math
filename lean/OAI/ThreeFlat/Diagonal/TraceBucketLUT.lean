import OAI.ThreeFlat.Diagonal.TraceBucketReverse
import OAI.ThreeFlat.RAM.HistoryCompiledRows

namespace OAI
/-! # One public ternary-table identifier per cell slot, shared by every lane -/

namespace ThreeFlat.Diagonal.TraceBitHeader

open Computability.VPVNP.BurstRAM LaneCursor
variable {F : Type*} [Fintype F] [CommRing F] {w p S f lane low : ℕ}
variable (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k : ℕ)

local notation "G" => TraceStaticRow.gateTable hF hw hp base f st r k (lane+low)
local notation "N" => network hF hw hp base st hs hf r k (lane+low)

/-- The initial trace table in its chronological cell ordering is repeated
at each site. Each field value therefore uses the same small library ID in
every copy of the row, independent of the program and the input. -/
theorem rectangular_table (fit : S+f ≤ 2^(1+(lane+low))) (row : Row lane low) (slot : Fin (G).cells) :
    (N).table ((rectangular hF hw hp base st hs hf r k fit).cell row slot)=(G).table slot := by
  change (G).table (finProdFinEquiv.symm (finProdFinEquiv (row.cast (Nat.pow_add 2 lane low).symm,slot))).2=_
  rw [Equiv.symm_apply_apply]

theorem rectangular_id (fit : S+f ≤ 2^(1+(lane+low))) (row : Row lane low) (slot : Fin (G).cells) :
    ((RAM.HistoryCompiledRows.library N).id ((rectangular hF hw hp base st hs hf r k fit).cell row slot)).val =
      ((RAM.HistoryCompiledRows.library G).id slot).val := by
  exact congrArg (fun t : (Fin 3→Bool)→F => (Fintype.equivFin _ t).val)
    (rectangular_table hF hw hp base st hs hf r k fit row slot)

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
