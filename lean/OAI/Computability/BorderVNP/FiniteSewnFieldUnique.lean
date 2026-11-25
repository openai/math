import OAI.Computability.BorderVNP.FiniteSewnFieldCopyCover

/-! # Uniqueness of source lanes under concatenation of sparse staging descriptors -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField

open scoped Classical

/-- A source ordinal belongs to this row's half-open old interval. -/
def Interval.Hits (p : Interval) (k : ℕ) : Prop := p.oldStart ≤ k ∧ k < p.oldStart+p.width

/-- Two descriptor occurrences share no original lane. This includes empty rows at any offset. -/
def Interval.Separate (p q : Interval) : Prop := ∀ k, p.Hits k → q.Hits k → False

/-- A separated cover selects exactly one physical list index, even when some descriptors
are empty or have equal source fields. -/
theorem Covers.unique_index {old next : ℕ} {xs : List Interval} {read : Fin old → Option (Fin next)}
    (covered : Covers xs read) (disjoint : xs.Pairwise Interval.Separate) (k : Fin old) :
    ∃! i : Fin xs.length, (xs.get i).Hits k.val := by
  obtain ⟨p,hp,j,hj,hk⟩ := covered.covers k
  obtain ⟨i,eq⟩ := List.mem_iff_get.mp hp
  have hit : (xs.get i).Hits k.val := by rw [eq]; unfold Interval.Hits; omega
  refine ⟨i,hit,?_⟩
  intro a ha
  rcases lt_trichotomy a i with h|h|h
  · exact False.elim ((List.pairwise_iff_get.mp disjoint a i h) _ ha hit)
  · exact h
  · exact False.elim ((List.pairwise_iff_get.mp disjoint i a h) _ hit ha)

/-- Filtering the reservations with zero physical width preserves the source map. -/
theorem Covers.keep_positive {old next : ℕ} {xs : List Interval} {read : Fin old → Option (Fin next)}
    (covered : Covers xs read) : Covers (xs.filter (fun p => decide (0 < p.width))) read := by
  refine ⟨fun p hp => covered.oldFit p (List.mem_filter.mp hp).1,
    fun p hp => covered.newFit p (List.mem_filter.mp hp).1,
    fun p hp => covered.agrees p (List.mem_filter.mp hp).1,?_⟩
  intro k
  obtain ⟨p,hp,j,hj,eq⟩ := covered.covers k
  exact ⟨p,List.mem_filter.mpr ⟨hp,decide_eq_true (Nat.zero_lt_of_lt hj)⟩,j,hj,eq⟩

/-- Relocating all rows by the same base preserves disjointness. -/
theorem Interval.Separate.atOffset {p q : Interval} (h : p.Separate q) (base : ℕ) :
    (SewnField.atOffset base p).Separate (SewnField.atOffset base q) := by
  intro k ha hb
  change base+p.oldStart ≤ k ∧ k < base+p.oldStart+p.width at ha
  change base+q.oldStart ≤ k ∧ k < base+q.oldStart+q.width at hb
  exact h (k-base) (by unfold Interval.Hits; omega) (by unfold Interval.Hits; omega)

/-- Assemble independently ordered source words. Their physical bases must identify a unique
word for every shared ordinal. Each word's internal row order is unrestricted. -/
theorem offsetBlocks_separate {ι : Type*} [Fintype ι] (width start : ι → ℕ) (chunks : ι → List Interval)
    (within : ∀ a p, p ∈ chunks a → p.oldStart+p.width ≤ width a)
    (unique : ∀ a b (i : Fin (width a)) (j : Fin (width b)), start a+i.val = start b+j.val → a=b)
    (each : ∀ a, (chunks a).Pairwise Interval.Separate) :
    (Finset.univ.toList.flatMap fun a => (chunks a).map (atOffset (start a))).Pairwise Interval.Separate := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun a _ => List.pairwise_map.mpr ((each a).imp fun h => h.atOffset _),?_⟩
  apply (Finset.univ.nodup_toList : (Finset.univ : Finset ι).toList.Pairwise (·≠·)).imp
  intro a b ne p hp q hq k hk hl
  obtain ⟨p,pm,rfl⟩ := List.mem_map.mp hp
  obtain ⟨q,qm,rfl⟩ := List.mem_map.mp hq
  have pc := within a p pm
  have qc := within b q qm
  change start a+p.oldStart ≤ k ∧ k < start a+p.oldStart+p.width at hk
  change start b+q.oldStart ≤ k ∧ k < start b+q.oldStart+q.width at hl
  exact ne (unique a b ⟨k-start a,by omega⟩ ⟨k-start b,by omega⟩ (by simp only; omega))

/-- The copy-major grouping of physical rows is disjoint on the whole old port word. -/
theorem copyIntervals_separate {copies width : ℕ} (chunks : Fin copies → List Interval)
    (within : ∀ a p, p ∈ chunks a → p.oldStart+p.width ≤ width) (each : ∀ a, (chunks a).Pairwise Interval.Separate) :
    (copyIntervals copies width chunks).Pairwise Interval.Separate := by
  apply offsetBlocks_separate (fun _ => width) (fun a => a.val*width) chunks within _ each
  intro a b i j h
  have eq : finProdFinEquiv (a,i) = finProdFinEquiv (b,j) := Fin.ext (by
    change i.val+width*a.val = j.val+width*b.val
    simpa only [Nat.add_comm,Nat.mul_comm] using h)
  exact congrArg Prod.fst (finProdFinEquiv.injective eq)

end Packing.SewnField

end BorderVNP
end Computability
end OAI
