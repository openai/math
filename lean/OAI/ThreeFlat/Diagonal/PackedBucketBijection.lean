import OAI.ThreeFlat.Diagonal.BucketIntervalCodes
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI
/-! # The packed pair coordinates form a bijection for every group -/

namespace ThreeFlat.Diagonal.PackedBucketBijection

open HistoryContraction BucketIntervalCodes TickGroupIntervals

variable {I : Type*}

/-- Counter for the single selected group during the original bucket scan. -/
def ordinal (group : I → ℕ) (g : ℕ) (offset : ℕ) : List (Bucket I) → ℕ → ℕ
  | [], _ => 0
  | b :: bs, x =>
    if group b.site = g then
      if b.lo ≤ x ∧ x < b.hi then 1+offset+(x-b.lo)
      else ordinal group g (offset+b.size) bs x
    else ordinal group g offset bs x

theorem pairCode_eq (group : I → ℕ) (g : ℕ) (acc : ℕ → ℕ) (bs : List (Bucket I)) (x : ℕ) :
    pairCode g x (intervals group acc bs) = ordinal group g (acc g) bs x := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    change (if (interval (BucketRows.row group acc b)).code g x = 0 then
      pairCode g x (intervals group (BucketRows.bump group acc b) bs)
      else (interval (BucketRows.row group acc b)).code g x) = _
    by_cases hg : group b.site = g
    · by_cases h : b.lo ≤ x ∧ x < b.hi
      · simp [ordinal,interval,BucketRows.row,Interval.code,hg,h.1,h.2]
      · simp [ordinal,interval,BucketRows.row,Interval.code,hg,h,ih,BucketRows.bump]
    · simp [ordinal,interval,BucketRows.row,Interval.code,hg,ih,BucketRows.bump,Function.update_of_ne (Ne.symm hg)]

private theorem bounds (group : I → ℕ) (g off x : ℕ) (bs : List (Bucket I)) :
    ordinal group g off bs x = 0 ∨
      off < ordinal group g off bs x ∧ ordinal group g off bs x ≤ off + BucketRows.count group bs g := by
  induction bs generalizing off with
  | nil => simp [ordinal]
  | cons b bs ih =>
    by_cases hg : group b.site = g
    · by_cases h : b.lo ≤ x ∧ x < b.hi
      · simp only [ordinal,ite_eq_left hg,ite_eq_left h,BucketRows.count,List.map_cons,List.sum_cons]
        unfold Bucket.size
        omega
      · obtain prior := ih (off+b.size)
        simp only [ordinal,ite_eq_left hg,ite_eq_right h,BucketRows.count,List.map_cons,List.sum_cons] at *
        omega
    · simpa [ordinal,BucketRows.count,hg] using ih off

theorem pairCode_le_count (group : I → ℕ) (bs : List (Bucket I)) (g x : ℕ) :
    pairCode g x (intervals group (fun _ => 0) bs) ≤ BucketRows.count group bs g := by
  rw [pairCode_eq]
  have h := bounds group g 0 x bs
  omega

def Disjoint (group : I → ℕ) (bs : List (Bucket I)) : Prop :=
  bs.Pairwise (fun b c => group b.site = group c.site →
    ∀ x, b.lo ≤ x → x < b.hi → c.lo ≤ x → x < c.hi → False)

private theorem exists_owner (group : I → ℕ) (g off x : ℕ) (bs : List (Bucket I))
    (live : ordinal group g off bs x ≠ 0) : ∃ b ∈ bs, overlaps group g x b := by
  classical
  by_contra! none
  have z := (code_zero_iff group (fun _ => off) bs g x).mpr none
  exact live ((pairCode_eq group g (fun _ => off) bs x).symm.trans z)

theorem unique_address (group : I → ℕ) (g : ℕ) (bs : List (Bucket I)) (disj : Disjoint group bs)
    (off k : ℕ) (hk : k < BucketRows.count group bs g) :
    ∃! x : ℕ, ordinal group g off bs x = 1+off+k := by
  induction bs generalizing off k with
  | nil => simp [BucketRows.count] at hk
  | cons b bs ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp disj
    by_cases hg : group b.site = g
    · have total : BucketRows.count group (b::bs) g = b.size+BucketRows.count group bs g := by
        simp [BucketRows.count,hg]
      rw [total] at hk
      by_cases small : k < b.size
      · have bound := small
        unfold Bucket.size at bound
        have inside : b.lo ≤ b.lo+k ∧ b.lo+k < b.hi := by omega
        refine ⟨b.lo+k,by simp [ordinal,hg,inside],?_⟩
        intro y hy
        by_cases hyi : b.lo ≤ y ∧ y < b.hi
        · simp only [ordinal,ite_eq_left hg,ite_eq_left hyi] at hy
          omega
        · simp only [ordinal,ite_eq_left hg,ite_eq_right hyi] at hy
          have := bounds group g (off+b.size) y bs
          omega
      · let j := k-b.size
        have hj : j < BucketRows.count group bs g := by dsimp [j]; omega
        obtain ⟨x,hx,unique⟩ := ih tail (off+b.size) j hj
        have eq : 1+(off+b.size)+j = 1+off+k := by dsimp [j]; omega
        have pos : ordinal group g (off+b.size) bs x ≠ 0 := by omega
        obtain ⟨c,hc,hg',hlo,hhi⟩ := exists_owner group g (off+b.size) x bs pos
        have nxi : ¬(b.lo ≤ x ∧ x < b.hi) := fun ins =>
          head c hc (hg.trans hg'.symm) x ins.1 ins.2 hlo hhi
        refine ⟨x,by simpa only [ordinal,ite_eq_left hg,ite_eq_right nxi,← eq] using hx,?_⟩
        intro y hy
        by_cases hyi : b.lo ≤ y ∧ y < b.hi
        · simp only [ordinal,ite_eq_left hg,ite_eq_left hyi] at hy
          unfold Bucket.size at small
          omega
        · apply unique y
          simpa only [ordinal,ite_eq_left hg,ite_eq_right hyi,eq] using hy
    · have ht : k < BucketRows.count group bs g := by simpa [BucketRows.count,hg] using hk
      simpa only [ordinal,ite_eq_right hg] using ih tail off k ht

/-- Every live physical bit corresponds to precisely one of the actual
packed pair coordinates. An empty group gives the unique empty equivalence. -/
noncomputable def equiv (group : I → ℕ) (g : ℕ) (bs : List (Bucket I)) (disj : Disjoint group bs) :
    {x : ℕ // pairCode g x (intervals group (fun _ => 0) bs) ≠ 0} ≃ Fin (BucketRows.count group bs g) := by
  let q := fun x => ordinal group g 0 bs x
  have code (x : ℕ) : pairCode g x (intervals group (fun _ => 0) bs) = q x :=
    pairCode_eq ..
  let f := fun x : {x : ℕ // pairCode g x (intervals group (fun _ => 0) bs) ≠ 0} =>
    (⟨q x.val-1, by
      have live : q x.val ≠ 0 := (code x.val) ▸ x.property
      have h := bounds group g 0 x.val bs
      change q x.val = 0 ∨ 0 < q x.val ∧ q x.val ≤ 0+BucketRows.count group bs g at h
      omega⟩ : Fin (BucketRows.count group bs g))
  apply Equiv.ofBijective f
  constructor
  · intro x y eq
    have h := congrArg Fin.val eq
    change q x.val-1 = q y.val-1 at h
    have xp : q x.val ≠ 0 := (code x.val) ▸ x.property
    have yp : q y.val ≠ 0 := (code y.val) ▸ y.property
    obtain ⟨z,_,only⟩ := unique_address group g bs disj 0 (f x).val (f x).isLt
    apply Subtype.ext
    apply (only x.val ?_).trans (only y.val ?_).symm
    · change q x.val = 1+0+(q x.val-1)
      omega
    · change q y.val = 1+0+(q x.val-1)
      omega
  · intro k
    obtain ⟨x,hx,_⟩ := unique_address group g bs disj 0 k.val k.isLt
    change q x = 1+0+k.val at hx
    have live : pairCode g x (intervals group (fun _ => 0) bs) ≠ 0 := by rw [code,hx]; omega
    refine ⟨⟨x,live⟩,Fin.ext ?_⟩
    change q x-1 = k.val
    omega

@[simp] theorem equiv_val (group : I → ℕ) (g : ℕ) (bs : List (Bucket I)) (disj : Disjoint group bs)
    (x : {x : ℕ // pairCode g x (intervals group (fun _ => 0) bs) ≠ 0}) :
    (equiv group g bs disj x).val = pairCode g x.val (intervals group (fun _ => 0) bs)-1 := by
  change ordinal group g 0 bs x.val-1 = _
  rw [pairCode_eq]

/-- The very same bijection on the finite physical memory. Containment of the
original intervals ensures every packed coordinate is visited on the sweep. -/
noncomputable def boundedEquiv (group : I → ℕ) (g : ℕ) (bs : List (Bucket I)) (disj : Disjoint group bs)
    (n : ℕ) (fit : ∀ b ∈ bs, b.hi ≤ n) :
    {x : Fin n // pairCode g x.val (intervals group (fun _ => 0) bs) ≠ 0} ≃ Fin (BucketRows.count group bs g) := by
  let src := intervals group (fun _ => 0) bs
  have bound (x : ℕ) (live : pairCode g x src ≠ 0) : x < n := by
    have L : ordinal group g 0 bs x ≠ 0 := (pairCode_eq group g (fun _ => 0) bs x) ▸ live
    obtain ⟨b,hb,_,_,hi⟩ := exists_owner group g 0 x bs L
    exact hi.trans_le (fit b hb)
  let forget : {x : Fin n // pairCode g x.val src ≠ 0} ≃ {x : ℕ // pairCode g x src ≠ 0} :=
    ⟨fun x => ⟨x.val.val,x.property⟩, fun x => ⟨⟨x.val,bound _ x.property⟩,x.property⟩,
      fun _ => rfl,fun _ => rfl⟩
  exact forget.trans (equiv group g bs disj)

noncomputable def chunkEquiv (group : I → ℕ) (g : ℕ) (bs : List (Bucket I)) (disj : Disjoint group bs)
    (chunks bits : ℕ) (fit : ∀ b ∈ bs, b.hi ≤ chunks*bits) :
    {i : Fin chunks × Fin bits // pairCode g (i.1.val*bits+i.2.val) (intervals group (fun _ => 0) bs) ≠ 0} ≃
      Fin (BucketRows.count group bs g) := by
  let flatten := (finProdFinEquiv : Fin chunks × Fin bits ≃ Fin (chunks*bits))
  refine (flatten.subtypeEquiv (q := fun j => pairCode g j.val (intervals group (fun _ => 0) bs) ≠ 0) ?_).trans
    (boundedEquiv group g bs disj (chunks*bits) fit)
  intro i
  change (_ ≠ 0) ↔ pairCode g (i.2.val+bits*i.1.val) (intervals group (fun _ => 0) bs) ≠ 0
  rw [Nat.add_comm i.2.val,Nat.mul_comm bits]

@[simp] theorem chunkEquiv_val (group : I → ℕ) (g : ℕ) (bs : List (Bucket I)) (disj : Disjoint group bs)
    (chunks bits : ℕ) (fit : ∀ b ∈ bs, b.hi ≤ chunks*bits)
    (i : {i : Fin chunks × Fin bits // pairCode g (i.1.val*bits+i.2.val) (intervals group (fun _ => 0) bs) ≠ 0}) :
    (chunkEquiv group g bs disj chunks bits fit i).val =
      pairCode g (i.val.1.val*bits+i.val.2.val) (intervals group (fun _ => 0) bs)-1 := by
  change ordinal group g 0 bs (i.val.2.val+bits*i.val.1.val)-1 = _
  rw [pairCode_eq,Nat.mul_comm bits,Nat.add_comm i.val.2.val]



end ThreeFlat.Diagonal.PackedBucketBijection

end OAI
