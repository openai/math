import OAI.Hierarchy.DescentOldOccurrencePrefix

namespace OAI
/-! # Cardinalities of the real source/destination buckets before whole-item selection -/

namespace Hierarchy.DescentOldOccurrenceRAM
open Computability.BorderVNP.Crossing DescentPacking
open scoped Classical BigOperators
noncomputable section
variable {d : ℕ} {P : Type*} {bits : P→ℕ} (N : Network d P bits)
    {C : Type} [Fintype C] [DecidableEq C] (core : Finset N.Edge) (home : N.Site→C)
local notation "T" => nativeTraffic N core home

omit [Fintype C] in
theorem traffic_eq (u : N.Site) (v : C) :
    T u v = count (fun e => e∈core ∧ N.src e=u ∧ home (N.dst e)=v) := by
  have mem_count (p : N.Edge → Prop) (e : N.Edge) :
      e ∈ Finset.univ.filter p ↔ p e := by simp
  change Fintype.card {e : (coreGraph N core).Edge // (coreGraph N core).src e=u ∧ home (N.dst e.val)=v} = _
  rw [←Finset.card_univ]
  apply Finset.card_bij (fun e _ => e.val.val)
  · intro e _
    exact (mem_count _ _).mpr ⟨e.val.property,e.property⟩
  · intro i _ j _ h
    exact Subtype.ext (Subtype.ext h)
  · intro e he
    obtain ⟨inCore,src,dst⟩ := (mem_count _ _).mp he
    exact ⟨⟨⟨e,inCore⟩,src,dst⟩,Finset.mem_univ _,rfl⟩

theorem filter_fibers {I J : Type*} [Fintype I] [Fintype J] (p : I → Prop) (key : I → J)
    (q : J → Prop) :
    (∑ j, if q j then count (fun i => p i ∧ key i=j) else 0) =
      count (fun i => p i ∧ q (key i)) := by
  classical
  rw [← Finset.sum_filter]
  simp only [count_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : p i <;> simp [hi]

theorem live_eq (u : N.Site) : live T u = count (fun e=>e∈core ∧ N.src e=u) := by
  simp only [live,traffic_eq]
  simpa only [ite_true,and_assoc,and_true] using filter_fibers
    (fun e=>e∈core ∧ N.src e=u) (fun e=>home (N.dst e)) (fun _=>True)

theorem thick_eq (color : N.Site → Bool) (c v : C) :
    Fintype.card (ThickPool T (thickList home color c) v)=
      count (fun e=> e∈core ∧ home (N.dst e)=v ∧ home (N.src e)=c ∧ color (N.src e)=true) := by
  have pool := thickPool_card (U := N.Site) (V := C) T (thickList home color c) v
  have amount_eq := colored_amount (U := N.Site) home color true c (fun u => T u v)
  refine pool.trans (amount_eq.trans ?_)
  have fibers := filter_fibers (fun e : N.Edge => e ∈ core ∧ home (N.dst e) = v)
    N.src (fun u => home u = c ∧ color u = true)
  refine Eq.trans ?_ (fibers.trans ?_)
  · apply Finset.sum_congr rfl
    intro u _
    by_cases hu : home u = c ∧ color u = true
    · simp only [ite_eq_left hu]
      exact (traffic_eq N core home u v).trans (count_congr (fun _ => by tauto))
    · simp only [ite_eq_right hu]
  · apply count_congr
    intro e
    tauto

omit [Fintype C] in
/-- Within one physical (old site, destination) fiber, parallel old cables
retain their original order; the unit ordinal is exactly its earlier row count. -/
theorem unit_eq (a : Atom T) :
    a.2.2.val = count (fun f=> f∈core ∧ N.src f=a.1 ∧ home (N.dst f)=a.2.1 ∧
      originalId N.Edge f < originalId N.Edge (PairRAM.original N core home a)) := by
  let dest := fun e : (coreGraph N core).Edge => home (N.dst e.val)
  let E := graphAtom (coreGraph N core) dest (coreId N core)
  let e := E.symm a
  have h := core_rank N core (fun x=>home (N.dst x)) e
  change ((E e).2.2).val = _ at h
  rw [show E e=a from E.apply_symm_apply a] at h
  have source : N.src e.val=a.1 := graphAtom_src (coreGraph N core) dest a (coreId N core)
  have target : home (N.dst e.val)=a.2.1 := graphAtom_dest (coreGraph N core) dest a (coreId N core)
  rw [source,target] at h
  rw [h]
  unfold count
  congr 1
  ext f
  simp [show PairRAM.original N core home a = e.val from rfl]

end
end Hierarchy.DescentOldOccurrenceRAM

end OAI
