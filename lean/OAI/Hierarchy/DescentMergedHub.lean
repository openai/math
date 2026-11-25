import OAI.Hierarchy.DescentHostDirectory

namespace OAI
/-! # Saturated hub colonies and the native contact of a merged hub -/

namespace Hierarchy.DescentHostDirectory

open DescentColonies
open scoped BigOperators Classical
noncomputable section

/-- All offsets of a true dyadic interval occur among the actual block addresses. -/
theorem interval_card_eq {k d : ℕ} (hd : d≤k) (x : Block k) :
    (interval d x).card=width k d := by
  apply le_antisymm (interval_card d x)
  have wp : 0<width k d := Nat.two_pow_pos _
  have size : width k d*2^d=2^k := by rw [width,←pow_add,Nat.sub_add_cancel hd]
  have room : width k d*group d x+width k d≤2^k := by
    rw [←Nat.mul_succ,←size]
    exact Nat.mul_le_mul_left _ (group_lt hd x)
  let point (t : Fin (width k d)) : Block k := ⟨width k d*group d x+t.val,by have := t.isLt;omega⟩
  have member (t) : point t∈interval d x := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change (width k d*group d x+t.val)/width k d=group d x
    rw [Nat.mul_add_div wp,Nat.div_eq_of_lt t.isLt,Nat.add_zero]
  let f (t : Fin (width k d)) : interval d x := ⟨point t,member t⟩
  have inj : Function.Injective f := by
    intro t s eqn
    have eqVal := congrArg (fun z : interval d x => z.val.val) eqn
    exact Fin.ext (Nat.add_left_cancel eqVal)
  simpa using Fintype.card_le_of_injective f inj

variable {k D a B g slots : ℕ} {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- Every uncapped source hub has load `B` at each block. Its actual leaf
in the heavy-and-propagated split construction has length exactly `2^a`. -/
theorem saturated_depth (load : V→Block k→ℕ) (adj : V→V→Prop)
    (limit : ∀v i,load v i≤B) (hub : V) (full : ∀i,load hub i=B) (positive : 0<B)
    (x : Block k) : depth load adj D a B limit hub x=k-a := by
  let d := depth load adj D a B limit hub x
  have small : d≤k-a := depth_le load adj D a B limit hub x
  have bound : width k d*B≤2^a*B := by
    have budget := leaf_load load adj D a B limit hub x
    change mass load hub d x≤_ at budget
    simpa only [mass,full,Finset.sum_const,nsmul_eq_mul,Nat.cast_id,interval_card_eq (show d≤k by omega)] using budget
  have exponent := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (Nat.le_of_mul_le_mul_right bound positive)
  change d=k-a
  omega

/-- Replacing the depth `k-a` hub leaf by its containing length-`2^g`
interval changes the native contact window by at most `g` levels. -/
theorem merged_hub_hops (near : V → Finset V) (load : V→Block k→ℕ) (limit : ∀v i,load v i≤B)
    {v hub : V} (edge : hub∈near v) (back : v∈near hub) (full : ∀i,load hub i=B)
    (positive : 0<B) (ag : a≤g) (gk : g≤k) (x : Block k) {m n : ℕ} (ms : m<slots) (ns : n<slots) :
    let d := depth load (fun p q=>q∈near p) D a B limit v x
    let here : Key V := (v,(d,group d x),m)
    let there : Key V := (hub,(k-g,group (k-g) x),n)
    there∈next near (D+g) slots here ∧ here∈next near (D+g) slots there := by
  let adj := fun (p q : V) => q∈near p
  let d := depth load adj D a B limit v x
  have hubDepth := saturated_depth (D:=D) (a:=a) load adj limit hub full positive x
  have nearDepth : d≤k-a+D := (neighbor_depth load adj D a B limit edge x).trans_eq (by rw [hubDepth])
  have farDepth : k-a≤d+D := hubDepth ▸ neighbor_depth load adj D a B limit back x
  have dk : d≤k := (depth_le load adj D a B limit v x).trans (Nat.sub_le ..)
  have high : d≤(k-g)+(D+g) := by omega
  have low : k-g≤d+(D+g) := by omega
  exact ⟨one_hop (.inr edge) dk (Nat.sub_le ..) high low ns x,
    one_hop (.inr back) (Nat.sub_le ..) dk low high ms x⟩

end
end Hierarchy.DescentHostDirectory

end OAI
