import OAI.Computability.BorderVNP.PackedInheritedStaging

/-! # Consecutive zero and equality intervals for exterior port sewing

A partial map of old lanes to new source lanes determines a zero clamp or
an equality at every old bit. A maximal consecutive interval with constant
translation uses a single sparse record, including a contiguous interval
of unoccupied lanes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField

open scoped Classical

/-- One interval of the old incidence word, either copied with unit stride
from a new public interval or pinned to zero throughout. -/
structure Interval where
  /-- First occupied lane in the predecessor word. -/
  oldStart : ℕ
  /-- Number of consecutive old lanes represented by this descriptor. -/
  width : ℕ
  /-- First new source lane, or a zero clamp for this entire interval. -/
  source : Option ℕ

/-- The interval descriptions really cover the complete partial input map. -/
structure Covers {old next : ℕ} (runs : List Interval) (read : Fin old → Option (Fin next)) : Prop where
  oldFit : ∀ p ∈ runs, p.oldStart+p.width ≤ old
  newFit : ∀ p ∈ runs, ∀ j, p.source = some j → j+p.width ≤ next
  agrees : ∀ p ∈ runs, ∀ i < p.width, ∀ k : Fin old, k.val = p.oldStart+i →
    (read k).map Fin.val = p.source.map (·+i)
  covers : ∀ k : Fin old, ∃ p ∈ runs, ∃ i < p.width, k.val = p.oldStart+i

private def start {α : Type*} [DecidableEq α] (label : ℕ → α) : ℕ → ℕ
  | 0 => 0
  | j+1 => if label (j+1) = label j then start label j else j+1

private theorem start_le {α : Type*} [DecidableEq α] (label : ℕ → α) (k : ℕ) : start label k ≤ k := by
  induction k with
  | zero => rfl
  | succ k ih => unfold start; split <;> omega

private theorem start_mono {α : Type*} [DecidableEq α] (label : ℕ → α) : Monotone (start label) := by
  apply monotone_nat_of_le_succ
  intro k
  have h := start_le label k
  rw [start]
  split <;> omega

private theorem start_idem {α : Type*} [DecidableEq α] (label : ℕ → α) (k : ℕ) :
    start label (start label k) = start label k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases h : label (k+1) = label k
    · simpa only [start,h,ite_true] using ih
    · simp only [start,h,ite_false]

private theorem label_start {α : Type*} [DecidableEq α] (label : ℕ → α) (k : ℕ) :
    label k = label (start label k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases h : label (k+1) = label k
    · simpa only [start,h,ite_true] using ih
    · simp only [start,h,ite_false]

private def slope {old next : ℕ} (read : Fin old → Option (Fin next)) (k : ℕ) : Option ℤ :=
  if h : k < old then (read ⟨k,h⟩).map (fun j => (j.val : ℤ)-k) else none

private def runStart {old next : ℕ} (read : Fin old → Option (Fin next)) (k : Fin old) : Fin old :=
  ⟨start (slope read) k.val,(start_le _ k.val).trans_lt k.isLt⟩

private def interval {old next : ℕ} (read : Fin old → Option (Fin next)) (k : Fin old) : Interval :=
  ⟨(runStart read k).val,k.val+1-(runStart read k).val,(read (runStart read k)).map Fin.val⟩

/-- Exactly the final lane of each maximal consecutive constant translation
contributes a row, in increasing order of that lane. Zero-clamped runs have a single absent translation. -/
noncomputable def intervals {old next : ℕ} (read : Fin old → Option (Fin next)) : List Interval :=
  ((Finset.univ.filter (fun k : Fin old => ∀ j : Fin old, runStart read j = runStart read k → j ≤ k)).sort).map
    (interval read)

private theorem interval_agrees {old next : ℕ} (read : Fin old → Option (Fin next)) (last : Fin old)
    (i : ℕ) (hi : i < (interval read last).width) (k : Fin old) (hk : k.val = (interval read last).oldStart+i) :
    (read k).map Fin.val = (interval read last).source.map (·+i) := by
  let l := runStart read last
  have hl : l.val ≤ last.val := start_le _ _
  change i < last.val+1-l.val at hi
  change k.val = l.val+i at hk
  have hkey : start (slope read) k.val = l.val := by
    apply le_antisymm
    · exact start_mono (slope read) (by omega : k.val ≤ last.val)
    · calc
        l.val = start (slope read) l.val := (start_idem (slope read) last.val).symm
        _ ≤ start (slope read) k.val := start_mono (slope read) (by omega : l.val ≤ k.val)
  have lab := label_start (slope read) k.val
  rw [hkey] at lab
  simp only [slope,k.isLt,l.isLt,dite_true,Fin.eta] at lab
  change (read k).map Fin.val = ((read l).map Fin.val).map (·+i)
  cases ha : read k <;> cases hb : read l <;> simp_all [Option.map_some,Option.map_none]
  omega

/-- The maximal intervals are a complete in-bounds cover of the actual
partial lane map, for all widths including zero. -/
theorem intervals_cover {old next : ℕ} (read : Fin old → Option (Fin next)) : Covers (intervals read) read := by
  have getLast (p : Interval) (hp : p ∈ intervals read) : ∃ j : Fin old, interval read j = p := by
    obtain ⟨j,_,hj⟩ := List.mem_map.mp hp
    exact ⟨j,hj⟩
  constructor
  · intro p hp
    obtain ⟨j,rfl⟩ := getLast p hp
    have h := start_le (slope read) j.val
    have hb := j.isLt
    simp only [interval,runStart]
    omega
  · intro p hp z hz
    obtain ⟨j,rfl⟩ := getLast p hp
    let l := runStart read j
    have hl : l.val ≤ j.val := start_le _ _
    have q := interval_agrees read j (j.val-l.val) (by change j.val-l.val < j.val+1-l.val; omega)
      j (by change j.val=l.val+(j.val-l.val); omega)
    rw [hz] at q
    cases hj : read j with
    | none => simp [hj] at q
    | some a =>
      simp [hj] at q
      have ha := a.isLt
      change z+(j.val+1-l.val) ≤ next
      omega
  · intro p hp
    obtain ⟨j,rfl⟩ := getLast p hp
    exact interval_agrees read j
  · intro k
    let members := Finset.univ.filter (fun j : Fin old => runStart read j = runStart read k)
    have hk : k ∈ members := by simp [members]
    let last := members.max' ⟨k,hk⟩
    have same : runStart read last = runStart read k := (Finset.mem_filter.mp (members.max'_mem ⟨k,hk⟩)).2
    have lastMem : interval read last ∈ intervals read := by
      apply List.mem_map.mpr
      refine ⟨last,(Finset.mem_sort _).mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩),rfl⟩
      intro j hj
      exact members.le_max' j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj.trans same⟩)
    have hk' : k.val ≤ last.val := members.le_max' k hk
    have hl : (runStart read last).val ≤ k.val := same ▸ start_le (slope read) k.val
    refine ⟨interval read last,lastMem,k.val-(runStart read last).val,?_,?_⟩
    · change k.val-(runStart read last).val < last.val+1-(runStart read last).val
      omega
    · exact (Nat.add_sub_of_le hl).symm

end Packing.SewnField

end BorderVNP
end Computability
end OAI
