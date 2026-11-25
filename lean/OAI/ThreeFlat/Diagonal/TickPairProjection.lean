import OAI.ThreeFlat.Diagonal.TickAuxProjection
import OAI.ThreeFlat.RAM.TickPairHeader

namespace OAI
/-! # The two contiguous physical halves of one group's pair proposal -/

namespace ThreeFlat.Diagonal.TickAuxiliary

variable {a cap n : ℕ} (fit : 1+cap+2*n ≤ a)
local notation "A" => RAM.TickPairHeader.layout cap n fit

theorem pair_width : (A).pairsEnd-(A).wiresEnd = n+n := by
  dsimp [RAM.TickPairHeader.layout]
  omega

def pairMerge (old new : Fin n → Bool) (j : Fin ((A).pairsEnd-(A).wiresEnd)) : Bool :=
  Fin.append old new (j.cast (pair_width fit))

def oldPair (x : Fin ((A).pairsEnd-(A).wiresEnd) → Bool) (j : Fin n) := x ((j.castAdd n).cast (pair_width fit).symm)
def newPair (x : Fin ((A).pairsEnd-(A).wiresEnd) → Bool) (j : Fin n) := x ((Fin.natAdd n j).cast (pair_width fit).symm)

@[simp] theorem oldPair_merge (x y : Fin n → Bool) : oldPair fit (pairMerge fit x y)=x := by
  funext j
  simp only [oldPair,pairMerge,Fin.cast_cast,Fin.cast_refl,id_eq,Fin.append_left]

@[simp] theorem newPair_merge (x y : Fin n → Bool) : newPair fit (pairMerge fit x y)=y := by
  funext j
  simp only [newPair,pairMerge,Fin.cast_cast,Fin.cast_refl,id_eq,Fin.append_right]

theorem merge_split (z : Fin ((A).pairsEnd-(A).wiresEnd) → Bool) :
    pairMerge fit (oldPair fit z) (newPair fit z) = z := by
  funext j
  let i := j.cast (pair_width fit)
  have h : ∀ k : Fin (n+n), Fin.append (oldPair fit z) (newPair fit z) k =
      z (k.cast (pair_width fit).symm) := by
    intro k
    exact Fin.addCases (fun a => by simp only [Fin.append_left,oldPair])
      (fun a => by simp only [Fin.append_right,newPair]) k
  exact h i

/-- The internal group proposal has one physical encoding, even for groups
without any owned external bits. -/
def pairEquiv : ((Fin n → Bool) × (Fin n → Bool)) ≃ (Fin ((A).pairsEnd-(A).wiresEnd) → Bool) where
  toFun v := pairMerge fit v.1 v.2
  invFun v := (oldPair fit v,newPair fit v)
  left_inv := by rintro ⟨x,y⟩; simp
  right_inv := merge_split fit

theorem oldPair_pin (bits : Fin a → Bool) (i : Fin n) :
    oldPair fit (project A bits).pairs i = bits ⟨1+cap+i.val,by have := i.isLt; omega⟩ := by
  rfl

theorem newPair_pin (bits : Fin a → Bool) (i : Fin n) :
    newPair fit (project A bits).pairs i = bits ⟨1+cap+n+i.val,by have := i.isLt; omega⟩ := by
  apply congrArg bits
  apply Fin.ext
  change (1+cap)+(n+i.val)=(1+cap+n)+i.val
  omega

end ThreeFlat.Diagonal.TickAuxiliary

end OAI
