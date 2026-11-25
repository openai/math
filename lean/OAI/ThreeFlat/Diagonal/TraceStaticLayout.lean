import OAI.ThreeFlat.Diagonal.TraceStaticTable
import OAI.ThreeFlat.Diagonal.TraceUniformLayout

namespace OAI
/-! # Row owners and XOR itinerary for the repeated public gate table -/

namespace ThreeFlat.Diagonal.TraceStaticRow

open Computability.VPVNP BurstRAM LaneCursor
open TracePhysical (laneRow flatRow offset)

variable {F : Type*} [CommRing F] [Fintype F] {w p r k S f d lane low : ℕ}

def displacement (hw : 3 ≤ w+1) (fit : S+f ≤ 2^(1+d)) (v : Fin (2^d)) :
    Port w p r k d → Fin (1+(d+d))
  | .inl j => TraceUniformRow.code (by omega) fit v j
  | .inr _ => 0

theorem displacement_reaches (hw : 3 ≤ w+1) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (fit : S+f ≤ 2^(1+d)) (base : ℕ) (v : Fin (2^d)) (a : Port w p r k d) :
    v.val = (TraceUniformRow.owner fit v (portSource hw hs hf base v a)).val ^^^
      (offset d (displacement hw fit v a)).val := by
  cases a with
  | inl j => exact TraceUniformRow.reaches (by omega) fit v j
  | inr j => simp [portSource, TraceUniformRow.owner,displacement,TracePhysical.offset_zero]

noncomputable def layout (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k : ℕ) (fit : S+f ≤ 2^(1+(lane+low))) :
    RowLayout (network hF hw hp base st hs hf r k (lane+low)) lane low (1+((lane+low)+(lane+low)))
      (gateTable hF hw hp base f st r k (lane+low)).cells :=
  TraceUniformRow.indexedLayout (Nat.pow_add ..)
    (fun _ => TraceCircuit.networkCells (gateTable hF hw hp base f st r k (lane+low))) _
    (laneRow ∘ TraceUniformRow.hiddenOwner fit) (laneRow ∘ TracePhysical.headerOwner fit)
    (laneRow ∘ offset (lane+low)) 0 (show ((laneRow ∘ offset (lane+low)) (0 : Fin _)).val = 0 from TracePhysical.offset_zero _) (fun v j =>
      displacement hw fit v ((Fintype.equivFin (Port w p r k (lane+low))).symm j)) (by
        intro v j
        change laneRow v = partner (sourceRow _ _ (laneRow v) _) _
        rw [TraceUniformRow.laneOwner]
        apply Fin.ext
        exact displacement_reaches hw hs hf fit base v ((Fintype.equivFin (Port w p r k (lane+low))).symm j))

theorem layout_pin (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k : ℕ) (fit : S+f ≤ 2^(1+(lane+low)))
    (j : Fin (S*w)) :
    ((layout hF hw hp base st hs hf r k fit).pinRow j).val = (finProdFinEquiv.symm j : Fin S × Fin w).1.val/2 := by
  unfold layout
  exact congrArg (fun h => ((h : Fin (S*w) → Row lane low) j).val)
    (TraceUniformRow.indexedLayout_pins _ _ _ _ _ _ _ _ _ _)

end ThreeFlat.Diagonal.TraceStaticRow

end OAI
