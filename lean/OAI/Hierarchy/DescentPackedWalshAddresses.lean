import OAI.Hierarchy.DescentPackedWalshCube
import OAI.Hierarchy.DescentGLScoreRAM

namespace OAI
/-! # Fixed serialization of every original binary difference for the conditional row selector -/
namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup
open scoped Classical
noncomputable section
variable {u l : ℕ}

def appendCube (u l : ℕ) : Cube u × Cube l ≃ Cube (u+l) where
  toFun s:=addr s.1 s.2
  invFun s:=(fun i=>s (finSumFinEquiv (.inl i)),fun i=>s (finSumFinEquiv (.inr i)))
  left_inv:=by rintro ⟨p,q⟩;apply Prod.ext <;> funext j <;> simp [addr]
  right_inv:=by
    intro f
    funext i
    obtain ⟨j,rfl⟩:=finSumFinEquiv.surjective i
    cases j <;> simp [addr]

def groupLane (u l : ℕ) : Fin (2^u) × Fin (2^l) ≃ Fin (2^(u+l)) :=
  finProdFinEquiv.trans (finCongr (by rw [pow_add]))

def difference (u l : ℕ) : DescentGL.Bits (u+l) ≃ Fin (2^(u+l)) :=
  (DescentWalshPhysical.coordinates (u+l)).trans ((appendCube u l).symm.trans
    ((Equiv.prodCongr (ordinal u) (ordinal l)).trans (groupLane u l)))

theorem difference_read (p : Cube u) (q : Cube l) :
    difference u l ((DescentWalshPhysical.coordinates (u+l)).symm (addr p q))=
      groupLane u l (ordinal u p,ordinal l q) := by
  change (difference u l) ((DescentWalshPhysical.coordinates _).symm ((appendCube u l) (p,q)))=_
  simp [difference]

theorem difference_back (i : Fin (2^u)) (j : Fin (2^l)) :
    (difference u l).symm (groupLane u l (i,j))=
      (DescentWalshPhysical.coordinates (u+l)).symm (addr ((ordinal u).symm i) ((ordinal l).symm j)) := by
  apply (difference u l).injective
  rw [Equiv.apply_symm_apply,difference_read,Equiv.apply_symm_apply,Equiv.apply_symm_apply]

theorem groupLane_val (i : Fin (2^u)) (j : Fin (2^l)) :
    (groupLane u l (i,j)).val=i.val*2^l+j.val := by
  change j.val+2^l*i.val=_
  rw [Nat.mul_comm i.val, Nat.add_comm]

/-- Only the final central column extractor needs this public change of enumeration. -/
def centralOrder (u l : ℕ) (i : Fin (2^(u+l))) : Fin (2^(u+l)) :=
  difference u l (DescentGLScoreRAM.vec i)

end
end Hierarchy.DescentPackedWalsh

end OAI
