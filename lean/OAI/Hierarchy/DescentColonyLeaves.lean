import OAI.Hierarchy.DescentColonyCover

namespace OAI
/-! # Number of actual leaves in the simultaneous colony partition -/

namespace Hierarchy.DescentColonies
open scoped Classical BigOperators
noncomputable section

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
variable (load : V → Block k → ℕ) (adj : V → V → Prop) (D a B : ℕ)
variable (limit : ∀v i,load v i≤B)

def leaves : Finset (V × ℕ × ℕ) :=
  Finset.univ.biUnion fun v => Finset.univ.image fun x : Block k =>
    let d := depth load adj D a B limit v x
    (v,d,group d x)

def marked : Finset (V × ℕ × ℕ) :=
  (Finset.range k).biUnion fun d => (splitSet load adj D a B d).image fun z => (z.1,d,z.2)

private def children (z : V × ℕ × ℕ) : Finset (V × ℕ × ℕ) :=
  {(z.1,z.2.1+1,2*z.2.2),(z.1,z.2.1+1,2*z.2.2+1)}

omit [Fintype V] in
private theorem children_card (z : V × ℕ × ℕ) : (children z).card≤2 := by
  apply (Finset.card_insert_le _ _).trans
  simp

private theorem leaf_subset :
    leaves load adj D a B limit ⊆ (Finset.univ.image fun v : V => (v,0,0)) ∪
      (marked load adj D a B).biUnion children := by
  intro z hz
  obtain ⟨v,_,hv⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hv
  let d := depth load adj D a B limit v x
  change (v,d,group d x)∈_
  by_cases h : d=0
  · have g : group d x=0 := by
      rw [h,group,width,Nat.sub_zero]
      exact Nat.div_eq_of_lt x.isLt
    rw [g,h]
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)
  · obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero h
    have small : i<d := by omega
    have sp := earlier_split load adj D a B limit v x small
    have imax : i<k := lt_of_lt_of_le small ((depth_le load adj D a B limit v x).trans (Nat.sub_le _ _))
    have original : (v,group i x)∈splitSet load adj D a B i :=
      Finset.mem_biUnion.mpr ⟨v,Finset.mem_univ _,Finset.mem_image.mpr
        ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,sp⟩,rfl⟩⟩
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨(v,i,group i x),Finset.mem_biUnion.mpr ⟨i,Finset.mem_range.mpr imax,
      Finset.mem_image.mpr ⟨(v,group i x),original,rfl⟩⟩,?_⟩
    have ancestor := ancestorId_group (k:=k) (d:=i) (j:=i+1) (Nat.le_succ _) x
    have ex : (k-i)-(k-(i+1))=1 := by omega
    simp only [ancestorId,ex,pow_one] at ancestor
    rw [hi,Nat.succ_eq_add_one]
    simp only [children,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,true_and]
    omega

/-- A root leaf accounts for one position. Every other leaf (even from a
propagated split) is one of the two actual children of a marked interval. -/
theorem leaf_count :
    (leaves load adj D a B limit).card ≤ Fintype.card V +
      2*∑ d∈Finset.range k,(splitSet load adj D a B d).card := by
  have roots : (Finset.univ.image fun v : V => (v,(0:ℕ),(0:ℕ))).card≤Fintype.card V := by
    simpa using Finset.card_image_le (s:=Finset.univ) (f:=fun v : V => (v,(0:ℕ),(0:ℕ)))
  have marks : (marked load adj D a B).card ≤ ∑d∈Finset.range k,(splitSet load adj D a B d).card :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_image_le)
  have childrenBound : ((marked load adj D a B).biUnion children).card ≤ 2*(marked load adj D a B).card := by
    apply Finset.card_biUnion_le.trans
    simpa [Nat.mul_comm] using (Finset.sum_le_sum (s:=marked load adj D a B) fun z _ => children_card z)
  calc
    _ ≤ _ := Finset.card_le_card (leaf_subset load adj D a B limit)
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add roots (childrenBound.trans (Nat.mul_le_mul_left 2 marks))

end
end Hierarchy.DescentColonies

end OAI
