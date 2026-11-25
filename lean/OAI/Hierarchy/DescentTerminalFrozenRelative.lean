import OAI.Computability.BorderVNP.FragmentBucketOrder
import OAI.Hierarchy.DescentTerminalPacketHomeRAM

namespace OAI
/-! # Per-home public row ranks from the smaller frozen roster -/
namespace Hierarchy.DescentTerminalExteriorPackets
open Computability.BorderVNP.FragmentBucket
open scoped Classical
noncomputable section
variable {n m R H : ℕ}

theorem contiguous_prior (eqn : n=m*R) (tag : Fin m→Fin H) (home : Fin n→Fin H)
    (group : Fin n→Fin m) (ordinal : ∀i,(group i).val=i.val/R) (src : ∀i,home i=tag (group i))
    (z : Fin n) : prior home z.val (home z)=prior tag (group z).val (home z)*R+z.val%R := by
  have pos : 0<R := by
    by_contra! h
    have hn : n=0 := by simpa [Nat.eq_zero_of_le_zero h] using eqn
    have := z.isLt
    omega
  let c:=home z
  have segment (g : Fin m) (k : ℕ) (hk : k≤R) :
      prior home (g.val*R+k) c=prior home (g.val*R) c+(if tag g=c then k else 0) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have live : k<R := by omega
      have edge:=Nat.mul_le_mul_right R (Nat.succ_le_of_lt g.isLt)
      rw [Nat.succ_mul] at edge
      let a : Fin n:=⟨g.val*R+k,by omega⟩
      have actual : group a=g := by
        apply Fin.ext
        rw [ordinal]
        change (g.val*R+k)/R=g.val
        rw [Nat.mul_comm g.val R,Nat.mul_add_div pos,Nat.div_eq_of_lt live,Nat.add_zero]
      change prior home (a.val+1) c=_
      rw [prior_step,src a,actual]
      change prior home (g.val*R+k) c+_=_
      rw [ih (Nat.le_of_lt live)]
      split <;> simp_all only [ite_true,ite_false]; omega
  have boundary (g : ℕ) (hg : g≤ m) : prior home (g*R) c=prior tag g c*R := by
    induction g with
    | zero => simp [prior_zero]
    | succ g ih =>
      let a : Fin m:=⟨g,by omega⟩
      have next := segment a R le_rfl
      rw [Nat.succ_mul]
      change prior home (a.val*R+R) c=prior tag (a.val+1) c*R
      rw [next,prior_step,ih (by omega),Nat.add_mul]
      split <;> simp_all only [ite_true,ite_false,zero_mul,one_mul] <;> rfl
  let g:=group z
  have value : z.val=g.val*R+z.val%R := by
    rw [show g.val=z.val/R from ordinal z,Nat.div_add_mod']
  have h:=segment g (z.val%R) (Nat.le_of_lt (Nat.mod_lt _ pos))
  rw [←value,boundary g.val g.isLt.le,ite_eq_left (src z).symm] at h
  exact h

/-- The calendar's slab-major physical address is globally consecutive across slab boundaries. -/
theorem calendar_quotient (E j rest kept : ℕ) (low : j≤kept) (top : kept≤j+(j+rest)) (i : Fin (E*2^(j+rest))) :
    DescentTerminalPacketHomeRAM.calendar E j rest kept i=i.val/2^(kept-j) := by
  let x:=finProdFinEquiv.symm i
  have ord : i.val=x.2.val+2^(j+rest)*x.1.val :=
    (congrArg Fin.val (finProdFinEquiv.apply_symm_apply i)).symm
  have split : 2^(j+rest)=2^(kept-j)*2^(j+(j+rest)-kept) := by rw [←pow_add];congr 1;omega
  change x.2.val/2^(kept-j)+2^(j+(j+rest)-kept)*x.1.val=i.val/2^(kept-j)
  rw [ord]
  generalize x.1.val=b
  generalize x.2.val=a
  rw [split,Nat.mul_assoc,Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]

end
end Hierarchy.DescentTerminalExteriorPackets

end OAI
