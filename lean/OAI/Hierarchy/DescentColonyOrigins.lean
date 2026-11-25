import OAI.Hierarchy.DescentColonies

namespace OAI
/-! # Tracking a propagated split to its actual heavy interval -/

namespace Hierarchy.DescentColonies
open scoped Classical BigOperators
noncomputable section

variable {V : Type*} {k : ℕ}

/-- A directed route of precisely n neighbor propagations. Parent steps at one
site use no edge and are accounted for separately in the dyadic depth. -/
inductive Reach (adj : V → V → Prop) (v : V) : ℕ → V → Prop
  | nil : Reach adj v 0 v
  | snoc {n u z} : Reach adj v n u → adj u z → Reach adj v (n+1) z

/-- For each actual propagated mark there is an initial heavy interval and an
actual neighbor path whose hop count times D fits between their depths. The
target interval is its unique ancestor at the given depth. -/
theorem Split.origin {load : V → Block k → ℕ} {adj : V → V → Prop} {D cap : ℕ}
    {v d x} (split : Split load adj D cap v d x) :
    ∃ (w : V) (j : ℕ) (y : Block k) (hops : ℕ),
      cap<mass load w j y ∧ Reach adj w hops v ∧ d+hops*D≤j ∧ group d y=group d x := by
  induction split with
  | heavy heavy => exact ⟨_,_,_,0,heavy,.nil,by simp,rfl⟩
  | @parent v d x _ ih =>
    obtain ⟨w,j,y,hops,heavy,reach,budget,alignment⟩ := ih
    exact ⟨w,j,y,hops,heavy,reach,by omega,group_ancestor (Nat.le_succ d) alignment⟩
  | @neighbor v z d x edge _ ih =>
    obtain ⟨w,j,y,hops,heavy,reach,budget,alignment⟩ := ih
    exact ⟨w,j,y,hops+1,heavy,reach.snoc edge,by rw [Nat.add_mul]; omega,
      group_ancestor (Nat.le_add_right d D) alignment⟩
  | same eq _ ih =>
    obtain ⟨w,j,y,hops,heavy,reach,budget,alignment⟩ := ih
    exact ⟨w,j,y,hops,heavy,reach,budget,alignment.trans eq⟩

/-- At fixed target position and depth each heavy source interval can account
for only one ancestor, namely its prefix. -/
def initialIds (load : V → Block k → ℕ) (cap : ℕ) (v : V) (j : ℕ) : Finset ℕ :=
  (Finset.univ.filter fun x => cap<mass load v j x).image (group j)

/-- The address of the actual dyadic ancestor given only the source identifier. -/
def ancestorId (k d j : ℕ) (id : ℕ) := id / (2^((k-d)-(k-j)))

theorem ancestorId_group {j d : ℕ} (le : d≤j) (x : Block k) :
    ancestorId k d j (group j x)=group d x := by
  unfold ancestorId group width
  rw [Nat.div_div_eq_div_mul,←pow_add]
  congr 2
  omega

/-- For a given source and depths there are no more possible target ancestors
than heavy source intervals, or than the number of dyadic intervals at the
target depth. These are the two competing caps in the colony estimate. -/
theorem ancestor_card (load : V → Block k → ℕ) (cap : ℕ) (v : V) {j d : ℕ}
    (hd : d≤j) (hj : j≤k) :
    ((initialIds load cap v j).image (ancestorId k d j)).card ≤
      min (initialIds load cap v j).card (2^d) := by
  apply le_min Finset.card_image_le
  apply (Finset.card_le_card ?_).trans_eq (Finset.card_range (2^d))
  intro a ha
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨x,_hx,rfl⟩ := Finset.mem_image.mp ht
  rw [ancestorId_group hd,Finset.mem_range,group]
  apply (Nat.div_lt_iff_lt_mul (show 0<width k d from Nat.two_pow_pos _)).mpr
  unfold width
  rw [←pow_add,show d+(k-d)=k by omega]
  exact x.isLt

end
end Hierarchy.DescentColonies

end OAI
