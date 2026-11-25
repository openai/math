import OAI.Computability.BorderVNP.CubeISARowAccumSubtotals

/-! # The ordered packet and singleton streams of a declaration row

Packets appear in the order of the native mixed-radix trial counter. Each
accepted singleton pair contributes its bit offsets in increasing order
before the next pair starts. The two orientations of a strict row have
disjoint singleton streams.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open Physical Owned
open scoped BigOperators

variable {n d : ℕ}

/-- The packet stream emitted by the ascending counter for this strict row. -/
def packetVisits (blocks : ℕ) (i : Fin (n+1)) (s : Symbols d) : List (Packet n d blocks) :=
  (List.finRange (packetTrials n d blocks)).filterMap (packetTrial i s)

/-- The two nested ascending native loops for one orientation of a singleton row. -/
def singleVisits (blocks width : ℕ) (i : Fin (n+1)) (a b : Fin d) : List (SingleSlot n d blocks width) :=
  (List.finRange (singlePairTrials n d)).flatMap fun t =>
    (List.finRange (blocks*width)).filterMap (singleTrial i a b t)

/-- The counter obtained from the packet's remaining symbol pairs, orientation and block. -/
def packetOrdinal {blocks : ℕ} (i : Fin (n+1)) (p : Packet n d blocks) : Fin (packetTrials n d blocks) :=
  (packetDigits n d blocks).symm (((fun j => (p.1.1 (i.succAbove j)).val),p.1.2),p.2)

/-- The pair counter reconstructed by removing the grouping coordinate from the two labels. -/
def singleCounter {blocks width : ℕ} (i : Fin (n+1)) (z : SingleSlot n d blocks width) : Fin (singlePairTrials n d) :=
  (singleOtherLabels n d).symm (i.removeNth z.1.val.1,i.removeNth z.1.val.2)

/-- The linear ordinal of the singleton in its two nested loops, with the bit offset varying fastest. -/
def singleOrdinal {blocks width : ℕ} (i : Fin (n+1)) (z : SingleSlot n d blocks width) : ℕ :=
  (singleCounter i z).val*(blocks*width)+z.2.val

private theorem packet_hit {blocks : ℕ} (i : Fin (n+1)) (s : Symbols d) (t : Fin (packetTrials n d blocks))
    (p : Packet n d blocks) (h : packetTrial i s t = some p) : p.1.1 i = s ∧ packetOrdinal i p = t := by
  unfold packetTrial at h
  split at h
  · rename_i ht
    cases Option.some.inj h
    exact ⟨(packetRowEquiv i s ⟨t,ht⟩).property,congrArg Subtype.val ((packetRowEquiv i s).symm_apply_apply ⟨t,ht⟩)⟩
  · contradiction

private theorem single_hit {blocks width : ℕ} (i : Fin (n+1)) (a b : Fin d) (t : Fin (singlePairTrials n d))
    (j : Fin (blocks*width)) (z : SingleSlot n d blocks width) (h : singleTrial i a b t j = some z) :
    (z.1.val.1 i = a ∧ z.1.val.2 i = b) ∧ singleCounter i z = t ∧ z.2 = j := by
  obtain ⟨hx,hj⟩ := (singleTrial_some_iff i a b t j z).mp h
  have hs := (singleOrderedPairs i a b t).property
  rw [hx] at hs
  refine ⟨hs,?_,hj.symm⟩
  change (singleOrderedPairs i a b).symm ⟨z.1.val,hs⟩ = t
  rw [← (show singleOrderedPairs i a b t = ⟨z.1.val,hs⟩ from Subtype.ext hx), Equiv.symm_apply_apply]

/-- A packet is emitted exactly on the strict row of its grouping symbols. -/
theorem mem_packetVisits (blocks : ℕ) (i : Fin (n+1)) (s : Symbols d) (p : Packet n d blocks) :
    p ∈ packetVisits blocks i s ↔ p.1.1 i = s := by
  simp only [packetVisits,List.mem_filterMap,List.mem_finRange,true_and]
  constructor
  · rintro ⟨t,ht⟩; exact (packet_hit i s t p ht).1
  · intro hp
    exact ((packetTrial_exactly_once (width := 0) i s p).mpr ((packet_itemRow_eq_iff i s p).mpr hp)).exists

/-- The ordered singleton scan emits precisely the slots with its designated source and destination symbols. -/
theorem mem_singleVisits (blocks width : ℕ) (i : Fin (n+1)) (a b : Fin d) (z : SingleSlot n d blocks width) :
    z ∈ singleVisits blocks width i a b ↔ z.1.val.1 i = a ∧ z.1.val.2 i = b := by
  simp only [singleVisits,List.mem_flatMap,List.mem_filterMap,List.mem_finRange,true_and]
  constructor
  · rintro ⟨t,j,h⟩; exact (single_hit i a b t j z h).1
  · intro hz
    let x := (singleOrderedEquiv blocks width i a b).symm ⟨z,hz⟩
    have hx : singleOrderedEquiv blocks width i a b x = ⟨z,hz⟩ := Equiv.apply_symm_apply ..
    exact ⟨x.1.val,x.2,by simp only [singleTrial,dite_eq_left x.1.property,hx]⟩

/-- Every successive packet in the emitted list has a strictly larger actual trial ordinal. -/
theorem packetVisits_sorted (blocks : ℕ) (i : Fin (n+1)) (s : Symbols d) :
    (packetVisits blocks i s).Pairwise (fun p q => packetOrdinal i p < packetOrdinal i q) := by
  apply (List.pairwise_lt_finRange _).filterMap
  intro t u h p hp q hq
  rw [(packet_hit i s t p hp).2,(packet_hit i s u q hq).2]; exact h

/-- Both the outer pair counter and the inner bit scan preserve strict linear order. -/
theorem singleVisits_sorted (blocks width : ℕ) (i : Fin (n+1)) (a b : Fin d) :
    (singleVisits blocks width i a b).Pairwise (fun z y => singleOrdinal i z < singleOrdinal i y) := by
  unfold singleVisits
  rw [List.pairwise_flatMap]
  constructor
  · intro t _
    apply (List.pairwise_lt_finRange _).filterMap
    intro j k hj z hz y hy
    obtain ⟨_,ht,hj'⟩ := single_hit i a b t j z hz
    obtain ⟨_,hu,hk'⟩ := single_hit i a b t k y hy
    simp only [singleOrdinal,ht,hu,hj',hk',Nat.add_lt_add_iff_left]
    exact hj
  · apply (List.pairwise_lt_finRange _).imp
    intro t u htu z hz y hy
    obtain ⟨j,_,hj⟩ := List.mem_filterMap.mp hz
    obtain ⟨k,_,hk⟩ := List.mem_filterMap.mp hy
    obtain ⟨_,ht,hj'⟩ := single_hit i a b t j z hj
    obtain ⟨_,hu,hk'⟩ := single_hit i a b u k y hk
    simp only [singleOrdinal,ht,hu,hj',hk']
    have hm := Nat.mul_le_mul_right (blocks*width) (show t.val+1 ≤ u.val from htu)
    rw [Nat.succ_mul] at hm
    exact (Nat.add_lt_add_left j.isLt _).trans_le (hm.trans (Nat.le_add_right ..))

/-- No packet can be emitted twice. -/
theorem packetVisits_nodup (blocks : ℕ) (i : Fin (n+1)) (s : Symbols d) : (packetVisits blocks i s).Nodup :=
  (packetVisits_sorted blocks i s).imp fun h e => (ne_of_lt h) (congrArg (packetOrdinal i) e)

/-- No physical singleton bit can be emitted twice. -/
theorem singleVisits_nodup (blocks width : ℕ) (i : Fin (n+1)) (a b : Fin d) : (singleVisits blocks width i a b).Nodup :=
  (singleVisits_sorted blocks width i a b).imp fun h e => (ne_of_lt h) (congrArg (singleOrdinal i) e)

/-- The two orientations taken together emit exactly the singletons of the unordered row. -/
theorem mem_singleVisits_append (blocks width : ℕ) (i : Fin (n+1)) (a b : Fin d) (z : SingleSlot n d blocks width) :
    z ∈ singleVisits blocks width i a b ++ singleVisits blocks width i b a ↔
      itemRow i (.inr z : Item n d blocks width) = Sym2.mk a b := by
  rw [List.mem_append,mem_singleVisits,mem_singleVisits]
  exact Sym2.eq_iff.symm

/-- On a strict row the two orientations visit disjoint slots, so concatenating
both lists retains uniqueness. -/
theorem singleVisits_append_nodup (blocks width : ℕ) (i : Fin (n+1)) (a b : Fin d) (hab : a ≠ b) :
    (singleVisits blocks width i a b ++ singleVisits blocks width i b a).Nodup := by
  refine List.nodup_append.mpr ⟨singleVisits_nodup ..,singleVisits_nodup ..,?_⟩
  intro z hz y hy e
  subst y
  exact hab (((mem_singleVisits ..).mp hz).1.symm.trans ((mem_singleVisits ..).mp hy).1)

private theorem visitSum {X R : Type*} [Fintype X] [DecidableEq X] [AddCommMonoid R]
    (xs : List X) (row : X → Prop) [DecidablePred row] (nd : xs.Nodup) (mem : ∀ x, x ∈ xs ↔ row x) (f : X → R) :
    (xs.map f).sum = ∑ x : {x // row x}, f x.val := by
  have hs : xs.toFinset = Finset.univ.filter row := by ext x; simp [mem x]
  rw [← List.sum_toFinset f nd,hs,Finset.sum_subtype (p := row) _ (fun _ => by simp) f]

/-- An additive observable on the emitted packet list equals its sum on the physical row subtype. -/
theorem packetVisits_sum {R : Type*} [AddCommMonoid R] (blocks : ℕ) (i : Fin (n+1)) (s : Symbols d)
    (f : Packet n d blocks → R) :
    ((packetVisits blocks i s).map f).sum = ∑ p : {p : Packet n d blocks // p.1.1 i = s}, f p.val :=
  visitSum _ _ (packetVisits_nodup blocks i s) (mem_packetVisits blocks i s) f

/-- An additive observable on the emitted singleton list equals its sum on the ordered physical row subtype. -/
theorem singleVisits_sum {R : Type*} [AddCommMonoid R] (blocks width : ℕ) (i : Fin (n+1)) (a b : Fin d)
    (f : SingleSlot n d blocks width → R) :
    ((singleVisits blocks width i a b).map f).sum =
      ∑ z : {z : SingleSlot n d blocks width // z.1.val.1 i = a ∧ z.1.val.2 i = b}, f z.val :=
  visitSum _ _ (singleVisits_nodup blocks width i a b) (mem_singleVisits blocks width i a b) f

/-- The three consecutive strict-row streams contribute precisely the physical
row subtotal at every proposed cut coordinate. -/
theorem strictVisits_subtotal {blocks h K : ℕ} (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (i j : Fin (n+1)) (sym : Symbols d) :
    ((packetVisits blocks i sym).map fun p => crossCount b s select (.inl p) j).sum +
      ((singleVisits blocks (h*b) i sym.val.1 sym.val.2).map fun z => crossCount b s select (.inr z) j).sum +
      ((singleVisits blocks (h*b) i sym.val.2 sym.val.1).map fun z => crossCount b s select (.inr z) j).sum =
      subtotals itemRow (crossCount b s select) i (Sym2.mk sym.val.1 sym.val.2) j := by
  rw [← RowAccum.strictRow_subtotal b s select i j sym,packetVisits_sum,singleVisits_sum,singleVisits_sum,
    Nat.add_assoc,Fintype.sum_sum_type]
  congr 1
  · exact (Equiv.sum_comp (packetRowEquiv (blocks := blocks) i sym)
      (fun p => crossCount b s select (.inl p.val) j)).symm
  · exact congrArg₂ (· + ·)
      (Equiv.sum_comp (singleOrderedEquiv blocks (h*b) i sym.val.1 sym.val.2)
        (fun z => crossCount b s select (.inr z.val) j)).symm
      (Equiv.sum_comp (singleOrderedEquiv blocks (h*b) i sym.val.2 sym.val.1)
        (fun z => crossCount b s select (.inr z.val) j)).symm

/-- One ordered singleton stream gives the entire diagonal-row subtotal. -/
theorem diagonalVisits_subtotal {blocks h K : ℕ} (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (i j : Fin (n+1)) (a : Fin d) :
    ((singleVisits blocks (h*b) i a a).map fun z => crossCount b s select (.inr z) j).sum =
      subtotals itemRow (crossCount b s select) i (Sym2.mk a a) j := by
  rw [← RowAccum.diagonalRow_subtotal b s select i j a,singleVisits_sum]
  exact (Equiv.sum_comp (singleOrderedEquiv blocks (h*b) i a a)
    (fun z => crossCount b s select (.inr z.val) j)).symm

end Cube.Scatter

end BorderVNP
end Computability
end OAI
