import OAI.Hierarchy.DescentPackedWalshRow
import OAI.Hierarchy.DescentWalshPhysical

namespace OAI
/-! # The native high-row and low-lane Walsh indices are the original bit coordinates -/
namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
variable {u l b : ℕ}

def addr (p : Cube u) (q : Cube l) : Cube (u+l) :=
  fun i=>Sum.elim p q (finSumFinEquiv.symm i)

def axis (i : Fin (u+l)) : Axis u l := finSumFinEquiv.symm i

@[simp] theorem addr_low (p : Cube u) (q : Cube l) (j : Fin l) :
    addr p q (finSumFinEquiv (.inr j))=q j := by simp [addr]
@[simp] theorem addr_high (p : Cube u) (q : Cube l) (j : Fin u) :
    addr p q (finSumFinEquiv (.inl j))=p j := by simp [addr]

theorem changed (i : Fin (u+l)) (p : Cube u) (q : Cube l) (flag : Bool) :
    addr (above (axis i) p flag) (below (axis i) q flag)=Function.update (addr p q) i flag := by
  obtain ⟨j,rfl⟩:=finSumFinEquiv.surjective i
  funext z
  obtain ⟨t,rfl⟩:=finSumFinEquiv.surjective z
  have separated (a : Fin u) (z : Fin l) : Fin.castAdd l a≠Fin.natAdd u z := by
    intro same
    have hv:=congrArg Fin.val same
    change a.val=u+z.val at hv
    have ha:=a.isLt
    omega
  have reverse (a : Fin u) (z : Fin l) : Fin.natAdd u z≠Fin.castAdd l a := (separated a z).symm
  cases j <;> cases t <;> simp [axis,above,below,addr,Function.update_apply,separated,reverse]

theorem sign_at (i : Fin (u+l)) (p : Cube u) (q : Cube l) :
    subtractAt (axis i) (upperSign (axis i) p) q=addr p q i := by
  obtain ⟨j,rfl⟩:=finSumFinEquiv.surjective i
  cases j <;> simp [addr,axis,subtractAt,upperSign]

def shaped (x : Cube (u+l)→Cell b) : Cube u→Cube l→Cell b := fun p q=>x (addr p q)

theorem step_shaped (x : Cube (u+l)→Cell b) (i : Fin (u+l)) :
    step (axis i) (shaped x)=shaped (DescentWalshPhysical.layer i x) := by
  funext p q
  simp [shaped,step,sign_at,changed,DescentWalshPhysical.layer]

end
end Hierarchy.DescentPackedWalsh

end OAI
