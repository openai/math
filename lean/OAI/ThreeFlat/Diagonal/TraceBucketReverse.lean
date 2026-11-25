import OAI.ThreeFlat.Diagonal.LaneCursorReverse
import OAI.ThreeFlat.Diagonal.TraceBitNetwork

namespace OAI
/-! # The receiver address of a reserved trace wire is row-major -/

namespace ThreeFlat.Diagonal
open Computability.VPVNP BurstRAM LaneCursor

namespace TraceUniformRow

theorem indexedLayout_at_cell {F : Type*} {lane low t b q P o n c : ℕ} (ht : t = 2^lane*2^low)
    (rows : Fin t → Fin c → TraceCircuit.Cell F n q) (inp : Fin t → Fin q → BitSource b P)
    (hidden : Fin b → Row lane low) (pins : Fin P → Row lane low)
    (off : Fin o → Row lane low) (base : Fin o) (hbase : (off base).val=0)
    (idx : Fin t → Fin q → Fin o) (ok : ∀ v j,
      v.cast ht = partner (sourceRow hidden pins (v.cast ht) (inp v j)) (off (idx v j)))
    (row : Row lane low) (slot : Fin c) :
    (indexedLayout ht rows inp hidden pins off base hbase idx ok).cellAddress
        (finProdFinEquiv (row.cast ht.symm,slot))=(row,slot) := by
  subst t
  exact finProdFinEquiv.symm_apply_apply _

end TraceUniformRow

namespace TraceBitHeader

variable {F : Type*} [Fintype F] [CommRing F] {w p S f lane low : ℕ}

/-- The receiver ordinal is row times local gate count plus local gate slot.
It can be read by the existing arithmetic eleven-word record emitter. -/
noncomputable def rawRectangular (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1)
    (hp : p ≤ 2^(w+1)) (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (r k : ℕ) (fit : S+f ≤ 2^(1+(lane+low))) :
    (rawLayout hF hw hp base st hs hf r k fit).Rectangular where
  cell row slot := finProdFinEquiv (row.cast (Nat.pow_add 2 lane low).symm,slot)
  at_cell row slot := by
    change (TraceStaticRow.layout hF hw hp base st hs hf r k fit).cellAddress _=_
    unfold TraceStaticRow.layout
    apply TraceUniformRow.indexedLayout_at_cell

noncomputable def rectangular (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1)
    (hp : p ≤ 2^(w+1)) (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (r k : ℕ) (fit : S+f ≤ 2^(1+(lane+low))) :
    (layout hF hw hp base st hs hf r k fit).Rectangular where
  cell := (rawRectangular hF hw hp base st hs hf r k fit).cell
  at_cell := (rawRectangular hF hw hp base st hs hf r k fit).at_cell

theorem rectangular_cell_val (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1)
    (hp : p ≤ 2^(w+1)) (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (r k : ℕ) (fit : S+f ≤ 2^(1+(lane+low))) (row : Row lane low)
    (slot : Fin (TraceStaticRow.gateTable hF hw hp base f st r k (lane+low)).cells) :
    ((rectangular hF hw hp base st hs hf r k fit).cell row slot).val =
      row.val*(TraceStaticRow.gateTable hF hw hp base f st r k (lane+low)).cells+slot.val := by
  change slot.val+_=_; ac_rfl

end TraceBitHeader
end ThreeFlat.Diagonal

end OAI
