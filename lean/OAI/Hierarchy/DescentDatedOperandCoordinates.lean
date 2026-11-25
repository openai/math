import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Numeric selection keys in the ordinary dated operand reader -/
namespace Hierarchy.DescentDatedOperandCoordinates
open DescentSIMDLookup
noncomputable section

def pair (U V : ℕ) (hi lo : ℕ) :=
  if 0<hi ∧ hi≤U ∧ 0<lo ∧ lo≤V then (hi-1)*V+lo else 0

theorem pair_at {U V : ℕ} (i : Fin U) (j : Fin V) :
    pair U V (i.val+1) (j.val+1)=(finProdFinEquiv (i,j)).val+1 := by
  have valid : (0:ℕ) < i.val+1 ∧ i.val+1 ≤ U ∧ (0:ℕ) < j.val+1 ∧ j.val+1 ≤ V :=
    ⟨Nat.succ_pos _,i.isLt,Nat.succ_pos _,j.isLt⟩
  rw [pair,ite_eq_left valid]
  simp only [Nat.add_sub_cancel,finProdFinEquiv_apply_val]
  ring

theorem pair_le (U V hi lo : ℕ) : pair U V hi lo≤U*V := by
  unfold pair
  split
  · rename_i h
    have step:hi-1+1≤U:=by omega
    have bound:=Nat.mul_le_mul_right V step
    rw [Nat.add_mul,Nat.one_mul] at bound
    omega
  · exact Nat.zero_le _

@[simp] theorem pair_zero_left (U V lo : ℕ) : pair U V 0 lo=0 := by simp [pair]
@[simp] theorem pair_zero_right (U V hi : ℕ) : pair U V hi 0=0 := by simp [pair]

/-- On a carried actor read the old operand by the original peer and first
parallel-grain serial. Only a cable pointer has an entry in this family. -/
def oldName (paths blocks degree cap actor kind path block peer first : ℕ) :=
  if actor=1 ∧ kind=1 then
    pair paths (blocks*(degree*cap)) (path+1)
      (pair blocks (degree*cap) (block+1) (pair degree cap (peer+1) (first+1)))
  else 0

theorem old_name_at {P B D C : ℕ} (p : Fin P) (x : Fin B) (i : Fin D) (j : Fin C) :
    oldName P B D C 1 1 p.val x.val i.val j.val=
      (finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (i,j)))).val+1 := by
  unfold oldName
  rw [ite_eq_left (show (1:ℕ)=1 ∧ (1:ℕ)=1 from ⟨rfl,rfl⟩),pair_at,pair_at,pair_at]

/-- The previous wire carries its own signed orientation. On its source
face the last rotor choice means stay, while a target reads the measured
old peer (already one-based). An absent signed slot yields a zero key. -/
def previousPath (paths degree actor path oldSlot neighbor target : ℕ) :=
  if actor=1 ∧ oldSlot≠0 then
    pair paths (degree+1) (path+1) (if target=1 then neighbor else degree+1)
  else 0

theorem stay_at {P D : ℕ} (p : Fin P) (old neighbor : ℕ) (positive : old≠0) :
    previousPath P D 1 p.val old neighbor 0=(finProdFinEquiv (p,Fin.last D)).val+1 := by
  simpa [previousPath,positive] using pair_at p (Fin.last D)

theorem peer_at {P D : ℕ} (p : Fin P) (old : ℕ) (j : Fin D) (positive : old≠0) :
    previousPath P D 1 p.val old (j.val+1) 1=(finProdFinEquiv (p,j.castSucc)).val+1 := by
  simpa [previousPath,positive] using pair_at p j.castSucc

/-- The newborn predecessor ordinal points directly at the first member
of its original pair. A carried cable obtains its source from the path
comparison directory. -/
def sourcePath (actor rawPath reached : ℕ) :=
  if actor=1 then reached else if actor=2 then rawPath+1 else 0

def matched (P B C path block old mode : ℕ) :=
  pair P (B*(C*3)) path (pair B (C*3) (block+1) (pair C 3 old (mode+1)))

def anchorKey (P B C actor kind path block retainedSlot retainedTarget bornSlot bornSide : ℕ) :=
  if kind≠1 then 0 else
    if actor=1 then matched P B C path block retainedSlot (if retainedTarget=1 then 1 else 0)
    else if actor=2 then matched P B C path block (bornSlot+1) (if bornSide=1 then 2 else 0)
    else 0

theorem matched_at {P B C : ℕ} (p : Fin P) (x : Fin B) (old : Fin C) (mode : Fin 3) :
    matched P B C (p.val+1) x.val (old.val+1) mode.val=
      (finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (old,mode)))).val+1 := by
  simp only [matched,pair_at]

theorem carried_at {P B C : ℕ} (p : Fin P) (x : Fin B) (old : Fin C) (target : Bool) (bs side : ℕ) :
    anchorKey P B C 1 1 (p.val+1) x.val (old.val+1) target.toNat bs side=
      (finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (old,(if target then 1 else 0:Fin 3))))).val+1 := by
  cases target
  · simpa [anchorKey,Bool.toNat] using matched_at p x old (0:Fin 3)
  · simpa [anchorKey,Bool.toNat] using matched_at p x old (1:Fin 3)

theorem born_at {P B C : ℕ} (p : Fin P) (x : Fin B) (old : Fin C) (second : Bool) (saved target : ℕ) :
    anchorKey P B C 2 1 (p.val+1) x.val saved target old.val second.toNat=
      (finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (old,(if second then 2 else 0:Fin 3))))).val+1 := by
  cases second
  · simpa [anchorKey,Bool.toNat] using matched_at p x old (0:Fin 3)
  · simpa [anchorKey,Bool.toNat] using matched_at p x old (2:Fin 3)

/-- The matcher already returned role zero for either original in a
newborn. Its measured primitive mouth supplies the actual branch there. -/
def rawSocket (P O actor path anchor mouthRole : ℕ) :=
  pair P O path (if actor=2 ∧ anchor≠0 then anchor+mouthRole else anchor)

theorem raw_at {P C B : ℕ} (p : Fin P) (x : Fin B) (old : Fin C) (role : Fin 11) :
    rawSocket P (B*(C*11)) 1 (p.val+1) ((x.val*C+old.val)*11+role.val+1) 0=
      (finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (old,role)))).val+1 := by
  have addr:(finProdFinEquiv (x,finProdFinEquiv (old,role))).val=(x.val*C+old.val)*11+role.val := by
    simp only [finProdFinEquiv_apply_val];ring
  simpa only [rawSocket,show (1:ℕ)≠2 by decide,false_and,ite_false,addr] using pair_at p (finProdFinEquiv (x,finProdFinEquiv (old,role)))

theorem born_raw_at {P C B : ℕ} (p : Fin P) (x : Fin B) (old : Fin C) (role : Fin 11) :
    rawSocket P (B*(C*11)) 2 (p.val+1) ((x.val*C+old.val)*11+1) role.val=
      (finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (old,role)))).val+1 := by
  have addr:(finProdFinEquiv (x,finProdFinEquiv (old,role))).val=(x.val*C+old.val)*11+role.val := by
    simp only [finProdFinEquiv_apply_val];ring
  have yes : (x.val*C+old.val)*11+1≠0:=by omega
  simpa [rawSocket,yes,addr,Nat.add_right_comm] using pair_at p (finProdFinEquiv (x,finProdFinEquiv (old,role)))

end
end Hierarchy.DescentDatedOperandCoordinates

end OAI
