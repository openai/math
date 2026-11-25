import OAI.Hierarchy.DescentColonyOrigins

namespace OAI
/-! # A finite cover of all propagated split addresses -/

namespace Hierarchy.DescentColonies
open scoped BigOperators Classical
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def next (adj : V → V → Prop) (v : V) : Finset V := Finset.univ.filter (adj v)

def frontier (adj : V → V → Prop) (v : V) : ℕ → Finset V
  | 0 => {v}
  | n+1 => (frontier adj v n).biUnion (next adj)

def ball (adj : V → V → Prop) (v : V) : ℕ → Finset V
  | 0 => {v}
  | n+1 => ball adj v n ∪ frontier adj v (n+1)

theorem frontier_card {Δ : ℕ} {adj : V → V → Prop}
    (degree : ∀v,(next adj v).card≤Δ) (v : V) (n : ℕ) :
    (frontier adj v n).card≤Δ^n := by
  induction n with
  | zero => simp [frontier]
  | succ n ih =>
    calc
      _ ≤ ∑w∈frontier adj v n,(next adj w).card := Finset.card_biUnion_le
      _ ≤ ∑_w∈frontier adj v n,Δ := Finset.sum_le_sum fun w _ => degree w
      _ ≤ Δ^(n+1) := by simpa [pow_succ] using Nat.mul_le_mul_right Δ ih

theorem ball_card {Δ : ℕ} {adj : V → V → Prop}
    (degree : ∀v,(next adj v).card≤Δ) (branch : 2≤Δ) (v : V) (n : ℕ) :
    (ball adj v n).card≤2*Δ^n := by
  induction n with
  | zero => simp [ball]
  | succ n ih =>
    calc
      _ ≤ (ball adj v n).card+(frontier adj v (n+1)).card := Finset.card_union_le _ _
      _ ≤ 2*Δ^n+Δ^(n+1) := Nat.add_le_add ih (frontier_card degree v _)
      _ ≤ _ := by rw [pow_succ]; nlinarith [Nat.mul_le_mul_right (Δ^n) branch]

theorem Reach.mem_frontier {adj : V → V → Prop} {v z : V} {n : ℕ} (h : Reach adj v n z) :
    z∈frontier adj v n := by
  induction h with
  | nil => simp [frontier]
  | snoc h edge ih => exact Finset.mem_biUnion.mpr ⟨_,ih,by simpa [next] using edge⟩

theorem frontier_subset_ball {adj : V → V → Prop} {v : V} {a b : ℕ} (le : a≤b) :
    frontier adj v a⊆ball adj v b := by
  induction b with
  | zero => simp_all [frontier,ball]
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le le with rfl | lt
    · exact Finset.subset_union_right
    · exact (ih (by omega)).trans Finset.subset_union_left

variable {k : ℕ} (load : V → Block k → ℕ) (adj : V → V → Prop) (D a B : ℕ)
variable (limit : ∀ v i, load v i≤B)

/-- The actual set of distinct propagated position/interval pairs at depth d. -/
def splitSet (d : ℕ) : Finset (V × ℕ) :=
  Finset.univ.biUnion fun v =>
    (Finset.univ.filter fun x => Split load adj D (2^a*B) v d x).image fun x => (v,group d x)

/-- All candidates produced by initial marks at one source and one depth. -/
def coverAt (w : V) (d j : ℕ) : Finset (V × ℕ) :=
  if d≤j then
    (ball adj w ((j-d)/D)) ×ˢ ((initialIds load (2^a*B) w j).image (ancestorId k d j))
  else ∅

include limit in
theorem split_covered (positive : 0<D) (d : ℕ) :
    splitSet load adj D a B d ⊆
      Finset.univ.biUnion (fun w : V => (Finset.range (k+1)).biUnion fun j =>
        coverAt load adj D a B w d j) := by
  intro p hp
  obtain ⟨v,_,hv⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨x,marked,rfl⟩ := Finset.mem_image.mp hv
  have hs := (Finset.mem_filter.mp marked).2
  obtain ⟨w,j,y,hops,heavy,reach,budget,align⟩ := hs.origin
  have deep : d≤j := by omega
  have jmax := split_shallow load adj D a B limit (Split.heavy (adj:=adj) (D:=D) heavy)
  have cnt : hops≤(j-d)/D := (Nat.le_div_iff_mul_le positive).2 (by omega)
  apply Finset.mem_biUnion.mpr
  refine ⟨w,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨j,Finset.mem_range.mpr (by omega),?_⟩⟩
  rw [coverAt,ite_eq_left deep]
  apply Finset.mem_product.mpr
  refine ⟨frontier_subset_ball cnt reach.mem_frontier,Finset.mem_image.mpr ⟨group j y,?_,?_⟩⟩
  · exact Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,heavy⟩,rfl⟩
  · exact (ancestorId_group deep y).trans align

theorem cover_card {Δ : ℕ} (degree : ∀v,(next adj v).card≤Δ) (branch : 2≤Δ)
    (w : V) {d j : ℕ} (le : d≤j) (jk : j≤k) :
    (coverAt load adj D a B w d j).card ≤
      (2*Δ^((j-d)/D))*min (initialIds load (2^a*B) w j).card (2^d) := by
  rw [coverAt,ite_eq_left le,Finset.card_product]
  exact Nat.mul_le_mul (ball_card degree branch w _) (ancestor_card load _ w le jk)

end
end Hierarchy.DescentColonies

end OAI
