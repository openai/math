import OAI.ThreeFlat.Diagonal.PhysicalStage

namespace OAI
/-! # Transport of physical runs and moves across equal dimensions -/

namespace ThreeFlat.Diagonal.PhysicalStage

noncomputable section
variable {F : Type} [Field F]

/-- Transport a move back across the equality of its displayed input lane counts. -/
def Move.recastInputLanes {d i j D rem : ℕ} (e : i=j) (A : State d i) :
    Move F (e ▸ A : State d j) D rem → Move F A D rem := by
  subst j
  exact id

namespace Program

def recast {d l l' : ℕ} (e : l=l') (A : State d l) : Run F (e ▸ A : State d l') → Run F A :=
  by subst l'; exact id

def recastMove {d l D D' L : ℕ} {A : State d l} (e : D=D') : Move F A D L → Move F A D' L :=
  by subst D'; exact id

end Program
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
