import OAI.ThreeFlat.Diagonal.LaneBucketNetwork
import OAI.ThreeFlat.Diagonal.LaneCursorReverse

namespace OAI
/-! # Constant-radix physical indices for the initial bucket forest -/

namespace ThreeFlat.Diagonal.LaneCursor.RowLayout

variable {F : Type*} {p k low offsets slots : ℕ} {N : BitNetwork F p} (P : RowLayout N (k+1) low offsets slots)

/-- Direct row-fast access within one bucket. Each physical source cell's
position is computed from its local low bits and local gate slot. -/
def laneCell (R : P.Rectangular) (lane : Lane (k+1)) :
    Fin (2^low) × Fin slots ≃ {c // P.cellLane c = lane} where
  toFun a := ⟨R.cell ((splitRow _ _).symm (lane,a.1)) a.2,
    by simp [cellLane,R.at_cell]⟩
  invFun c := ((splitRow _ _ (P.cellAddress c.val).1).2,(P.cellAddress c.val).2)
  left_inv a := by simp [R.at_cell]
  right_inv c := by
    apply Subtype.ext
    apply P.cellAddress.injective
    rw [R.at_cell]
    refine Prod.ext ?_ rfl
    apply (splitRow _ _).injective
    rw [Equiv.apply_symm_apply]
    exact Prod.ext c.property.symm rfl

def laneCellOrd (R : P.Rectangular) (lane : Lane (k+1)) :
    Fin (2^low*slots) ≃ {c // P.cellLane c = lane} := finProdFinEquiv.symm.trans (P.laneCell R lane)

/-- The tag decoder requires three mixed-radix divisions. -/
def tagOrder (offsets low slots : ℕ) : Fin (offsets*(2^low*(slots*3))) ≃ Tags offsets low slots :=
  finProdFinEquiv.symm.trans ((Equiv.refl _).prodCongr (finProdFinEquiv.symm.trans
    ((Equiv.refl _).prodCongr finProdFinEquiv.symm)))

/-- Only the two source-address maps for local external inputs and hidden
variables depend on the program's chosen trace bank. -/
def initialIndex (R : P.Rectangular) (lane : Lane (k+1)) {hiddenCount pinCount : ℕ}
    (hidden : Fin hiddenCount ≃ {i // (splitRow _ _ (P.hiddenRow i)).1 = lane})
    (pins : Fin pinCount ≃ {j // (splitRow _ _ (P.pinRow j)).1 = lane}) : BucketIndex P lane where
  h := hiddenCount
  x := pinCount
  c := 2^low*slots
  t := offsets*(2^low*(slots*3))
  hidden := hidden
  ext := pins
  cell := P.laneCellOrd R lane
  tag := tagOrder offsets low slots
  probe := P.reverseProbe R lane
  probe_some := P.reverseProbe_iff R lane

end ThreeFlat.Diagonal.LaneCursor.RowLayout

end OAI
