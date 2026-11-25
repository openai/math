import OAI.Computability.BorderVNP.FiniteSewnFieldRuns

/-! # Staging a terminal program's original input across exterior sewing

The predecessor's incidence word becomes part of its private bank. Maximal
live runs are tied to their actual source intervals and maximal vacant
runs are zero-pinned. These records force a unique filling at every
public input and retain every successful original observation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField

open CellSparse Inherited
open scoped BigOperators Classical
open private bits_left bits_right from OAI.Computability.BorderVNP.PackedInheritedStaging

/-- Absolute sparse equality or zero descriptor for this interval of the old input. -/
def Interval.record (s : Site) (p : Interval) : Record :=
  match p.source with
  | none => .zero 1 p.width ⟨s.work+p.oldStart,0,1⟩
  | some j => .equal 1 p.width ⟨s.work+p.oldStart,0,1⟩ ⟨s.size+j,0,1⟩

/-- The prior program is retained and its prior input is now uniquely
staged by the physical sewn interval rows. -/
def stage (s : Site) (n : ℕ) (runs : List Interval) : Site :=
  ⟨s.size,n,s.boxes,(runs.map (Interval.record s)) :: s.layers⟩

/-- The actual records appear in old-to-new order and each interval has one descriptor. -/
theorem stage_rows (s : Site) (n : ℕ) (runs : List Interval) :
    (stage s n runs).rows = s.rows ++ runs.map (Interval.record s) := by
  simp [stage,Site.rows,List.flatten_append]

/-- Adding the staging descriptors preserves the complete ordered factor visit list. -/
theorem stage_occurrences (s : Site) (n : ℕ) (runs : List Interval) :
    (stage s n runs).directory.occurrences = s.directory.occurrences := by
  let visit (r : Record) := match r with
    | .box id base copies stride => (List.range copies).flatMap fun i =>
      (s.boxes.getD id []).map (fun f => (⟨f,base+i*stride,i⟩ : Occurrence))
    | _ => []
  have noVisits (p : Interval) : visit (Interval.record s p) = [] := by
    cases h : p.source <;> simp [visit,Interval.record,h]
  have empty : (runs.flatMap (fun _ => ([] : List Occurrence))) = [] := by induction runs <;> simp_all
  change (stage s n runs).rows.flatMap visit = s.rows.flatMap visit
  simp only [stage_rows,List.flatMap_append,List.flatMap_map,noVisits,empty,List.append_nil]

private theorem stage_observe (s : Site) (n : ℕ) (runs : List Interval) (bank : ℕ → Bool) :
    (stage s n runs).observe bank = if ∀ p ∈ runs, (p.record s).Valid s.boxes bank then s.observe bank else none := by
  have obs : (stage s n runs).directory.observations bank = s.directory.observations bank := by
    unfold Directory.observations
    rw [stage_occurrences]
  simp only [Site.observe,stage_rows,List.forall_mem_append,List.forall_mem_map,obs]
  change (if (∀ r ∈ s.rows, r.Valid s.boxes bank) ∧ (∀ p ∈ runs, (p.record s).Valid s.boxes bank) then
    s.directory.observations bank else none) = _
  split_ifs <;> simp_all

private theorem interval_valid (s : Site) (p : Interval) (bank : ℕ → Bool) :
    (p.record s).Valid s.boxes bank ↔ ∀ i < p.width, bank (s.work+(p.oldStart+i)) =
      (p.source.map (·+i)).elim false (fun j => bank (s.size+j)) := by
  cases h : p.source <;>
    simp only [Interval.record,h,Record.Valid,zeroValid,equalValid,Port.atBit,Nat.mul_zero,Nat.add_zero,
      Nat.mul_one,Nat.add_assoc,Option.map_none,Option.map_some,Option.elim_none,Option.elim_some]
  all_goals exact ⟨fun hh => hh 0 (by decide),fun hh _ _ => hh⟩

private theorem stages_iff (s : Site) {n : ℕ} (runs : List Interval) (read : Fin s.incoming → Option (Fin n))
    (cover : Covers runs read) (bank : ℕ → Bool) :
    (∀ p ∈ runs, (p.record s).Valid s.boxes bank) ↔ ∀ k : Fin s.incoming,
      bank (s.work+k.val) = (read k).elim false (fun j => bank (s.size+j.val)) := by
  have entry (k : Fin s.incoming) : ((read k).map Fin.val).elim false (fun j => bank (s.size+j)) =
      (read k).elim false (fun j => bank (s.size+j.val)) := by cases read k <;> rfl
  constructor
  · intro h k
    obtain ⟨p,hp,i,hi,hk⟩ := cover.covers k
    rw [← entry k,cover.agrees p hp i hi k hk,hk]
    exact (interval_valid s p bank).mp (h p hp) i hi
  · intro h p hp
    apply (interval_valid s p bank).mpr
    intro i hi
    let k : Fin s.incoming := ⟨p.oldStart+i,(Nat.add_lt_add_left hi _).trans_le (cover.oldFit p hp)⟩
    have eqn := (h k).trans (entry k).symm
    rw [cover.agrees p hp i hi k rfl] at eqn
    exact eqn

/-- For every raw bit assignment the new stage is local, including its
zero clamps, shared destination lanes and all older observations. -/
theorem stage_local (s : Site) (loc : s.Local) {n : ℕ} (runs : List Interval)
    (read : Fin s.incoming → Option (Fin n)) (cover : Covers runs read) : (stage s n runs).Local := by
  intro a b h
  have old := loc a b (fun j hj => h j (hj.trans_le (Nat.le_add_right _ _)))
  have test : (∀ p ∈ runs, (p.record s).Valid s.boxes a) ↔ ∀ p ∈ runs, (p.record s).Valid s.boxes b := by
    rw [stages_iff s runs read cover,stages_iff s runs read cover]
    apply forall_congr'
    intro k
    have l := h (s.work+k.val) ((Nat.add_lt_add_left k.isLt _).trans_le (Nat.le_add_right _ _))
    rw [l]
    cases hk : read k with
    | none => rfl
    | some j =>
      simp only [Option.elim_some]
      rw [h (s.size+j.val) (Nat.add_lt_add_left j.isLt _)]
  simp only [stage_observe,propext test,old]

/-- Exactly one predecessor incidence assignment retains the original observation. -/
theorem stage_observe_bits (s : Site) (loc : s.Local) {n : ℕ} (runs : List Interval)
    (read : Fin s.incoming → Option (Fin n)) (cover : Covers runs read)
    (g : Fin s.work → Bool) (old : Fin s.incoming → Bool) (new : Fin n → Bool) :
    (stage s n runs).observe (bits (Fin.append g old) new) =
      if old = fun k => (read k).elim false new then s.observe (bits g old) else none := by
  let b := bits (Fin.append g old) new
  have l (k : Fin s.incoming) : b (s.work+k.val) = old k :=
    (bits_left (Fin.append g old) new (k.natAdd s.work)).trans (Fin.append_right g old k)
  have r (j : Fin n) : b (s.size+j.val) = new j := bits_right (Fin.append g old) new j
  have test : (∀ p ∈ runs, (p.record s).Valid s.boxes b) ↔ old = fun k => (read k).elim false new := by
    rw [stages_iff s runs read cover,funext_iff]
    apply forall_congr'
    intro k
    rw [l]
    cases read k <;> simp [r]
  have same : s.observe b = s.observe (bits g old) := loc _ _ fun i hi => by
    change i < s.work+s.incoming at hi
    rw [show b i = Fin.append g old ⟨i,hi⟩ from bits_left _ _ ⟨i,hi⟩,bits,dite_eq_left hi]
  rw [stage_observe]
  change (if ∀ p ∈ runs, (p.record s).Valid s.boxes b then s.observe b else none) = _
  by_cases h : old = fun k => (read k).elim false new
  · rw [ite_eq_left (test.mpr h),ite_eq_left h,same]
  · rw [ite_eq_right (fun hv => h (test.mp hv)),ite_eq_right h]

/-- Summing the new private tapes gives the old site's exact field value at
the selected sources, with zero for every missing old input lane. -/
theorem stage_value {K : Type*} [AddCommMonoid K] (s : Site) (loc : s.Local) {n : ℕ} (runs : List Interval)
    (read : Fin s.incoming → Option (Fin n)) (cover : Covers runs read)
    (weight : List (Bool × Option ℕ) → K) (new : Fin n → Bool) :
    (stage s n runs).value weight new = s.value weight (fun k => (read k).elim false new) := by
  let term (w : Fin (s.work+s.incoming) → Bool) :=
    ((stage s n runs).observe (bits w new)).elim 0 weight
  change (∑ w, term w) = _
  rw [← (Fin.appendEquiv (α := Bool) s.work s.incoming).sum_comp term,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro g _
  change (∑ old, ((stage s n runs).observe (bits (Fin.append g old) new)).elim 0 weight) = _
  simp_rw [stage_observe_bits s loc runs read cover]
  rw [Finset.sum_eq_single (fun k => (read k).elim false new)]
  · simp
  · intro old _ h
    simp [h]
  · simp

end Packing.SewnField

end BorderVNP
end Computability
end OAI
