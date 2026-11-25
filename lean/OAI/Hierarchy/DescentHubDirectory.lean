import OAI.Hierarchy.DescentMergedHub

namespace OAI
/-! # Coarsening the evenly saturated external hubs in the actual common directory -/

namespace Hierarchy.DescentHostDirectory
open DescentColonies DescentContacts
open scoped Classical
noncomputable section
variable {V : Type} [DecidableEq V]

def mergeHub (hub : V→Bool) (k g : ℕ) (x : Key V) : Key V :=
  if hub x.1 then (x.1,(k-g,x.2.1.2/2^(x.2.1.1-(k-g))),0) else x

omit [DecidableEq V] in
theorem merge_hub_read (hub : V→Bool) {k g a : ℕ} (ag : a≤g) (gk : g≤k)
    (v : V) (yes : hub v=true) (x : Block k) (slot : ℕ) :
    mergeHub hub k g (v,(k-a,group (k-a) x),slot)=(v,(k-g,group (k-g) x),0) := by
  have pow : width k (k-a)*2^((k-a)-(k-g))=width k (k-g) := by
    unfold width
    rw [←pow_add]
    congr 1
    omega
  simp [mergeHub,yes,DescentColonies.group,Nat.div_div_eq_div_mul,pow]

theorem possible_mono (d id u v U V : ℕ) (hu : u≤U) (hv : v≤V) :
    possible d id u v⊆possible d id U V := by
  apply Finset.union_subset_union
  · apply Finset.image_subset_image
    exact Finset.range_mono (by omega)
  · intro k hk
    obtain ⟨j,jh,hit⟩ := Finset.mem_biUnion.mp hk
    exact Finset.mem_biUnion.mpr ⟨j,Finset.range_mono (by omega : v+1≤V+1) jh,hit⟩

theorem widen_next (near : V→Finset V) {D W slots : ℕ} (larger : D≤W) (x : Key V) :
    next near D slots x⊆next near W slots x := by
  apply Finset.product_subset_product_right
  apply Finset.product_subset_product_left
  exact possible_mono _ _ _ _ _ _ larger larger

theorem widen_directory (near : V→Finset V) {D W slots h : ℕ} (larger : D≤W) (x : Key V) :
    directory near D slots h x⊆directory near W slots h x := by
  induction h with
  | zero => rfl
  | succ n ih =>
    intro v hv
    obtain ⟨i,reachable,nextStep⟩ := Finset.mem_biUnion.mp hv
    exact Finset.mem_biUnion.mpr ⟨i,ih reachable,widen_next near larger i nextStep⟩

theorem compose_directory (near : V→Finset V) {w slots s t : ℕ} {x y z : Key V}
    (a : y∈directory near w slots s x) (b : z∈directory near w slots t y) :
    z∈directory near w slots (s+t) x := by
  induction t generalizing z with
  | zero =>
    have eq : z=y := by simpa [directory] using b
    simpa [eq] using a
  | succ t ih =>
    obtain ⟨i,past,step⟩ := Finset.mem_biUnion.mp b
    exact extend (ih past) step

/-- Every actual old packed site is represented by its realized colony code.
Empty directory entries need no saturated-depth assumption. -/
theorem hub_hops (hub : V→Bool) (near : V→Finset V) {k g a D slots : ℕ}
    (ag : a≤g) (gk : g≤k) (x : Key V) (slot : x.2.2<slots)
    (saturated : hub x.1=true→∃b : Block k,x.2.1=(k-a,group (k-a) b)) :
    mergeHub hub k g x∈next near (D+g) slots x ∧ x∈next near (D+g) slots (mergeHub hub k g x) := by
  rcases x with ⟨v,⟨d,id⟩,m⟩
  cases hh : hub v with
  | false => simp only [mergeHub,hh,Bool.false_eq_true,ite_false];exact ⟨pad _ slot,pad _ slot⟩
  | true =>
    obtain ⟨b,eq⟩ := saturated hh
    cases eq
    rw [merge_hub_read hub ag gk v hh b m]
    exact ⟨one_hop (.inl rfl) (Nat.sub_le ..) (Nat.sub_le ..) (by omega) (by omega) (by omega) b,
      one_hop (.inl rfl) (Nat.sub_le ..) (Nat.sub_le ..) (by omega) (by omega) slot b⟩

theorem merged_cable_hops (hub : V→Bool) (near : V→Finset V) {k g a D slots : ℕ}
    (ag : a≤g) (gk : g≤k) {x y : Key V}
    (old : y∈directory near D slots 8 x)
    (xm : x.2.2<slots) (ym : y.2.2<slots)
    (xs : hub x.1=true→∃b : Block k,x.2.1=(k-a,group (k-a) b))
    (ys : hub y.1=true→∃b : Block k,y.2.1=(k-a,group (k-a) b)) :
    mergeHub hub k g y∈directory near (D+g) slots 10 (mergeHub hub k g x) := by
  have first : x∈directory near (D+g) slots 1 (mergeHub hub k g x) := by
    simpa [directory] using (hub_hops hub near ag gk x xm xs).2
  exact extend (compose_directory near first (widen_directory near (Nat.le_add_right D g) x old))
    (hub_hops hub near ag gk y ym ys).1

end
end Hierarchy.DescentHostDirectory

end OAI
