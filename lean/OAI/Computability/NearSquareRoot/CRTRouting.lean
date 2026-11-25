import OAI.Computability.NearSquareRoot.CRTIsomorphism

/-! # Balanced CRT merges on a padded box

A child permutation leaves its complementary coordinates fixed. Its inverse on the left
child recovers the controlling digits using just the left address. One parent merge then
performs independent translations on the right axes and fixes their padding.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRT

variable {d : ℕ} {a : Fin d → ℕ} {E : Fin d → Type}

/-- In-range coordinates are residues. Each axis can have its own set of padding addresses. -/
abbrev Address (a : Fin d → ℕ) (E : Fin d → Type) := ∀ i, ZMod (a i) ⊕ E i

abbrev Agrees (s : Finset (Fin d)) (x y : Address a E) :=
  ∀ i ∈ s, x i = y i

/-- A permutation confined to a block in both directions. In particular the inverse
decodes all digits in the block independently of every other block's current state. -/
structure BlockPerm (a : Fin d → ℕ) (E : Fin d → Type) (s : Finset (Fin d)) where
  perm : Equiv.Perm (Address a E)
  outside : ∀ x i, i ∉ s → perm x i = x i
  reads : ∀ x y, Agrees s x y → Agrees s (perm x) (perm y)
  inverseReads : ∀ x y, Agrees s x y → Agrees s (perm.symm x) (perm.symm y)

theorem BlockPerm.inverse_outside {s : Finset (Fin d)} (p : BlockPerm a E s)
    (x : Address a E) (i : Fin d) (h : i ∉ s) : p.perm.symm x i = x i := by
  simpa using (p.outside (p.perm.symm x) i h).symm

private theorem agreeOnSubset {s t : Finset (Fin d)} (h : s ⊆ t)
    {x y : Address a E} (e : Agrees t x y) : Agrees s x y :=
  fun i hi => e i (h hi)

/-- A disjoint family of local computations can be carried out simultaneously.
The coordinate formula is a parallel application of the two child maps. -/
def BlockPerm.parallel {l r : Finset (Fin d)} (left : BlockPerm a E l)
    (right : BlockPerm a E r) (hd : Disjoint l r) : BlockPerm a E (l ∪ r) where
  perm := left.perm.trans right.perm
  outside := by
    intro x i hi
    have h := Finset.notMem_union.mp hi
    exact (right.outside _ _ h.2).trans (left.outside _ _ h.1)
  reads := by
    intro x y h i hi
    by_cases hir : i ∈ r
    · apply right.reads _ _ _ i hir
      intro j hj
      have hjl : j ∉ l := fun h' => Finset.disjoint_left.mp hd h' hj
      rw [left.outside _ j hjl, left.outside _ j hjl]
      exact h j (Finset.mem_union_right _ hj)
    · obtain hil := (Finset.mem_union.mp hi).resolve_right hir
      change right.perm (left.perm x) i = right.perm (left.perm y) i
      rw [right.outside _ i hir, right.outside _ i hir]
      exact left.reads _ _ (agreeOnSubset Finset.subset_union_left h) i hil
  inverseReads := by
    intro x y h i hi
    by_cases hil : i ∈ l
    · apply left.inverseReads _ _ _ i hil
      intro j hj
      have hjr := Finset.disjoint_left.mp hd hj
      rw [right.inverse_outside _ j hjr, right.inverse_outside _ j hjr]
      exact h j (Finset.mem_union_left _ hj)
    · obtain hir := (Finset.mem_union.mp hi).resolve_left hil
      change left.perm.symm (right.perm.symm x) i = left.perm.symm (right.perm.symm y) i
      rw [left.inverse_outside _ i hil, left.inverse_outside _ i hil]
      exact right.inverseReads _ _ (agreeOnSubset Finset.subset_union_right h) i hir

/-- Rotate only valid axis positions. -/
def translate {m : ℕ} {V : Type} (v : ZMod m) : Equiv.Perm (ZMod m ⊕ V) :=
  Equiv.sumCongr (Equiv.addRight v) (Equiv.refl V)

/-- A controlled block layer, with independent single-axis tables on the targets. -/
def shear {l r : Finset (Fin d)} (hd : Disjoint l r)
    (delta : Address a E → ∀ i, ZMod (a i))
    (reads : ∀ x y, Agrees l x y → delta x = delta y) : BlockPerm a E (l ∪ r) := by
  let f (x : Address a E) : Address a E := fun i =>
    if i ∈ r then translate (delta x i) (x i) else x i
  let g (x : Address a E) : Address a E := fun i =>
    if i ∈ r then (translate (delta x i)).symm (x i) else x i
  have hf (x) : delta (f x) = delta x := reads _ _ fun i hi => ite_eq_right (Finset.disjoint_left.mp hd hi)
  have hg (x) : delta (g x) = delta x := reads _ _ fun i hi => ite_eq_right (Finset.disjoint_left.mp hd hi)
  refine ⟨⟨f, g, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x
    funext i
    change (if i ∈ r then (translate (delta (f x) i)).symm (f x i) else f x i) = x i
    by_cases hi : i ∈ r <;> simp [hi, hf, f]
  · intro x
    funext i
    change (if i ∈ r then translate (delta (g x) i) (g x i) else g x i) = x i
    by_cases hi : i ∈ r <;> simp [hi, hg, g]
  · intro x i hi
    exact ite_eq_right (Finset.notMem_union.mp hi).2
  · intro x y h i hi
    change f x i = f y i
    simp only [f, reads x y (agreeOnSubset Finset.subset_union_left h), h i hi]
  · intro x y h i hi
    change g x i = g y i
    simp only [g, reads x y (agreeOnSubset Finset.subset_union_left h), h i hi]

/-- Original digits are recovered by the inverse map of the *left child alone*. An
invalid left address gives the identity tables. -/
def mergeOffset [∀ i, NeZero (a i)] {l : Finset (Fin d)} (p : BlockPerm a E l)
    (x : Address a E) (i : Fin d) : ZMod (a i) :=
  if ∀ j ∈ l, (p.perm.symm x j).isLeft then
    weight a i * ((∑ j ∈ l, CRT.prefix a j *
      ((p.perm.symm x j).elim ZMod.val (fun _ => 0)) : ℕ) : ZMod (a i))
  else 0

theorem mergeOffset_reads [∀ i, NeZero (a i)] {l : Finset (Fin d)} (p : BlockPerm a E l)
    (x y : Address a E) (h : Agrees l x y) : mergeOffset p x = mergeOffset p y := by
  funext i
  have e := p.inverseReads _ _ h
  unfold mergeOffset
  have hg : (∀ j ∈ l, (p.perm.symm x j).isLeft) ↔ (∀ j ∈ l, (p.perm.symm y j).isLeft) := by
    constructor <;> intro h j hj
    · rw [← e j hj]; exact h j hj
    · rw [e j hj]; exact h j hj
  apply if_congr hg _ rfl
  congr 2
  exact Finset.sum_congr rfl fun j hj => by rw [e j hj]

/-- Parent execution consists of the two independent child permutations followed by one
layer of conditional rotations. -/
def merge [∀ i, NeZero (a i)] {l r : Finset (Fin d)} (p : BlockPerm a E l)
    (q : BlockPerm a E r) (hd : Disjoint l r) : BlockPerm a E (l ∪ r) := by
  let kids := p.parallel q hd
  let cross := shear hd (mergeOffset p) (mergeOffset_reads p)
  exact {
    perm := kids.perm.trans cross.perm
    outside := fun x i hi => (cross.outside _ _ hi).trans (kids.outside x i hi)
    reads := fun x y h => cross.reads _ _ (kids.reads x y h)
    inverseReads := fun x y h => kids.inverseReads _ _ (cross.inverseReads x y h)
  }


def partialRank (a : Fin d → ℕ) (s : Finset (Fin d)) (t : ∀ j, ZMod (a j)) : ℕ :=
  ∑ j ∈ s, CRT.prefix a j * (t j).val

/-- The permutation on the valid part of one interval, allowing arbitrary spectators. -/
def Computes {s : Finset (Fin d)} (p : BlockPerm a E s) : Prop :=
  ∀ (x : Address a E) (t : ∀ j, ZMod (a j)), (∀ j ∈ s, x j = Sum.inl (t j)) →
    ∀ i ∈ s, p.perm x i = Sum.inl
      (t i + weight a i * (partialRank a (s.filter (· < i)) t : ZMod (a i)))

def identityBlock (s : Finset (Fin d)) : BlockPerm a E s :=
  ⟨Equiv.refl _, fun _ _ _ => rfl, fun _ _ h => h, fun _ _ h => h⟩

theorem computes_leaf {s : Finset (Fin d)} (hs : s.card ≤ 1) :
    Computes (identityBlock s : BlockPerm a E s) := by
  intro x t h i hi
  have empty : s.filter (· < i) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    obtain ⟨hj, hji⟩ := Finset.mem_filter.mp hj
    exact hji.ne (Finset.card_le_one.mp hs j hj i hi)
  simpa [identityBlock, empty, partialRank] using h i hi

private theorem parallel_left {l r : Finset (Fin d)} (p : BlockPerm a E l)
    (q : BlockPerm a E r) (hd : Disjoint l r) (x : Address a E) :
    Agrees l ((p.parallel q hd).perm x) (p.perm x) := by
  intro i hi
  exact q.outside (p.perm x) i (Finset.disjoint_left.mp hd hi)

private theorem parallel_right {l r : Finset (Fin d)} (p : BlockPerm a E l)
    (q : BlockPerm a E r) (hd : Disjoint l r) (x : Address a E) :
    Agrees r ((p.parallel q hd).perm x) (q.perm x) := by
  apply q.reads
  exact fun i hi => p.outside x i (fun hl => Finset.disjoint_left.mp hd hl hi)

/-- The table generator may recover the left address from either the original child output
or the parallel pair of child outputs. The computed translation has exactly the rank weight
of the left interval. -/
theorem mergeOffset_eq [∀ i, NeZero (a i)] {l r : Finset (Fin d)} (p : BlockPerm a E l)
    (q : BlockPerm a E r) (hd : Disjoint l r) (x : Address a E) (t : ∀ j, ZMod (a j))
    (hx : ∀ j ∈ l, x j = Sum.inl (t j)) (i : Fin d) :
    mergeOffset p ((p.parallel q hd).perm x) i =
      weight a i * (partialRank a l t : ZMod (a i)) := by
  rw [mergeOffset_reads p _ _ (parallel_left p q hd x)]
  simp only [mergeOffset, Equiv.symm_apply_apply]
  have hv : ∀ j ∈ l, (x j).isLeft = true := fun j hj => by simp [hx j hj]
  rw [ite_eq_left_iff.mpr (fun h => (h hv).elim)]
  congr 2
  exact Finset.sum_congr rfl fun j hj => by rw [hx j hj]; rfl

/-- Correctness of one balanced CRT merge. The order hypothesis expresses adjacency
of the two children in the mixed-radix digit order. -/
theorem computes_merge [∀ i, NeZero (a i)] {l r : Finset (Fin d)} (p : BlockPerm a E l)
    (q : BlockPerm a E r) (hd : Disjoint l r) (order : ∀ j ∈ l, ∀ i ∈ r, j < i)
    (hp : Computes p) (hq : Computes q) : Computes (merge p q hd) := by
  intro x t hx i hi
  have xl : ∀ j ∈ l, x j = Sum.inl (t j) := fun j hj => hx j (Finset.mem_union_left _ hj)
  have xr : ∀ j ∈ r, x j = Sum.inl (t j) := fun j hj => hx j (Finset.mem_union_right _ hj)
  let u := (p.parallel q hd).perm x
  change (if i ∈ r then translate (mergeOffset p u i) (u i) else u i) = _
  by_cases hr : i ∈ r
  · have hl : l.filter (· < i) = l := Finset.filter_true_of_mem fun j hj => order j hj i hr
    have hsum : partialRank a ((l ∪ r).filter (· < i)) t =
        partialRank a l t + partialRank a (r.filter (· < i)) t := by
      rw [Finset.filter_union, hl, partialRank, Finset.sum_union]
      · rfl
      · exact hd.mono_right (Finset.filter_subset ..)
    dsimp only [u]
    rw [ite_eq_left hr, parallel_right p q hd x i hr, hq x t xr i hr, mergeOffset_eq p q hd x t xl,
      hsum, Nat.cast_add, mul_add]
    simp only [translate, Equiv.sumCongr_apply, Sum.map_inl, Equiv.coe_addRight]
    congr 1
    abel
  · have hl := (Finset.mem_union.mp hi).resolve_right hr
    have hempty : r.filter (· < i) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      obtain ⟨hj, hji⟩ := Finset.mem_filter.mp hj
      exact (order i hl j hj).not_gt hji
    dsimp only [u]
    rw [ite_eq_right hr, parallel_left p q hd x i hl, hp x t xl i hl, Finset.filter_union, hempty,
      Finset.union_empty]

end CRT

end NearSquareRoot
end Computability
end OAI
