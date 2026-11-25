import OAI.ThreeFlat.Diagonal.TracePhysicalLayout
import OAI.ThreeFlat.Diagonal.TraceArrayLayout

namespace OAI
/-! # The concrete physical verifier as a lane-cursor row layout -/

namespace ThreeFlat.Diagonal.TracePhysical

open LaneCursor
variable {F : Type*} {w r S f k low n c : ℕ}

def laneRow (i : Fin (2^(k+low))) : Row k low := Fin.cast (Nat.pow_add ..) i
def flatRow (v : Row k low) : Fin (2^(k+low)) := Fin.cast (Nat.pow_add ..).symm v

noncomputable def laneInput (hw : 2 ≤ w+1) (S f : ℕ) (v : Row k low)
    (j : Fin (Fintype.card (Port w r (k+low)))) :=
  address hw S f (flatRow v) ((Fintype.equivFin (Port w r (k+low))).symm j)

private theorem laneOwner (fits : S+f ≤ 2^(1+(k+low))) (v : Row k low)
    (z : BitSource (Fintype.card (Shared w r f (k+low))) (S*w)) :
    sourceRow (laneRow ∘ hiddenOwner fits) (laneRow ∘ headerOwner fits) v z =
       laneRow (owner fits (flatRow v) z) := by cases z <;> rfl

/-- The assembled physical trivalent circuit has the prescribed row owners,
a common public family of 1+2(k+low) offsets, and one cell slot per row gate. -/
noncomputable def laneLayout (hw : 2 ≤ w+1) (fits : S+f ≤ 2^(1+(k+low)))
    (rows : Row k low → Fin c → TraceCircuit.Cell F n (Fintype.card (Port w r (k+low)))) :
    RowLayout (TraceCircuit.assemble rows (laneInput hw S f)) k low (1+((k+low)+(k+low))) c :=
  TraceCircuit.arrayLayout rows (laneInput hw S f) (laneRow ∘ hiddenOwner fits)
    (laneRow ∘ headerOwner fits) (laneRow ∘ offset (k+low)) 0 (offset_zero _)
    (fun v j => code hw fits (flatRow v) ((Fintype.equivFin (Port w r (k+low))).symm j))
    (by
      intro v j
      rw [laneOwner]
      apply Fin.ext
      exact code_reaches hw fits (flatRow v) ((Fintype.equivFin (Port w r (k+low))).symm j))

/-- The public header ownership supplied to the cursor is exactly the
paired-word row of the relevant header word. -/
theorem laneLayout_pin (hw : 2 ≤ w+1) (fits : S+f ≤ 2^(1+(k+low)))
    (rows : Row k low → Fin c → TraceCircuit.Cell F n (Fintype.card (Port w r (k+low))))
    (j : Fin (S*w)) : ((laneLayout hw fits rows).pinRow j).val = (finProdFinEquiv.symm j : Fin S × Fin w).1.val / 2 :=
  rfl

end ThreeFlat.Diagonal.TracePhysical

end OAI
