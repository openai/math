import OAI.Hierarchy.FactorPinIntervals
import Mathlib.Data.List.Enum

namespace OAI
/-! # Scanning the original input intervals and emitting controller slots -/

namespace Hierarchy.FactorPinIntervals
open scoped BigOperators

variable {T : Type} {S N d : ℕ} (P : Layout T S N d)

/-- Source address and destination ordinal emitted by one pass over the input
stream, starting at the end of this tick's public header. -/
def Layout.emissions (t : T) : List (Fin S × ℕ) :=
  (P.inputBits t).zipIdx (P.header t).length

theorem Layout.emissions_correct (t : T) :
    ∀ r ∈ P.emissions t, P.tick r.1=t ∧ (P.slot r.1).val=r.2 := by
  exact (List.forall_mem_zipIdx (l:=P.inputBits t) (n:=(P.header t).length)
    (p:=fun r => P.tick r.1=t ∧ (P.slot r.1).val=r.2)).mpr
    (fun i hi => P.slot_get t ⟨i,hi⟩)

/-- Across all ticks the emitter writes one record per original input bit. -/
theorem Layout.emissions_total [Fintype T] : (∑ t, (P.emissions t).length)=S := by
  classical
  have count (t : T) :
      (P.emissions t).length=(Finset.univ.filter (fun j => P.tick j=t)).card := by
    rw [Layout.emissions,List.length_zipIdx,Layout.inputBits,
      ←List.toFinset_card_of_nodup (nodup_stream P.origin (P.distinct t))]
    congr 1
    ext j
    change j ∈ (stream P.origin (P.rows t)).toFinset ↔ j ∈ Finset.univ.filter (fun k => P.tick k=t)
    rw [List.mem_toFinset, mem_stream, Finset.mem_filter]
    simpa only [Finset.mem_univ, true_and, Layout.tick] using P.owns (P.origin j) t
  simp_rw [count]
  simpa using (Finset.card_eq_sum_card_fiberwise (s:=Finset.univ) (t:=Finset.univ)
    (f:=P.tick) (fun _ _ => Finset.mem_univ _)).symm

/-- The start of an original occurrence's pins is the header plus the total
length of the preceding occurrences. Its own within-occurrence index then
counts up without gaps. -/
theorem Layout.slot_prefix {t : T} {f : Fin N} {pre post : List (Fin N)}
    (split : P.rows t=pre++f::post) {j : Fin S} (own : P.origin j=f) :
    (P.slot j).val = (P.header t).length + (stream P.origin pre).length +
      (intervalBits P.origin f).idxOf j := by
  have inRow : f ∈ P.rows t := by simp [split]
  have ht : P.tick j=t := by
    change P.owner (P.origin j)=t
    exact own ▸ (P.owns f t).mp inRow
  have unique := P.distinct t
  rw [split] at unique
  have before : j ∉ stream P.origin pre := by
    intro hj
    exact (List.nodup_append.mp unique).2.2 f (own ▸ mem_stream.mp hj)
      f (List.mem_cons_self) rfl
  have here := mem_intervalBits.mpr own
  rw [P.slot_val ht,Layout.inputBits,split]
  simp only [stream,List.flatMap_append,List.flatMap_cons]
  change j ∉ pre.flatMap (intervalBits P.origin) at before
  rw [List.idxOf_append_of_notMem before,List.idxOf_append_of_mem here,Nat.add_assoc]

private theorem adjacent_index (xs : List (Fin S)) (ordered : xs.Pairwise (· < ·))
    {a b : Fin S} (ha : a ∈ xs) (hb : b ∈ xs) (step : b.val=a.val+1) :
    xs.idxOf b=xs.idxOf a+1 := by
  let i : Fin xs.length := ⟨xs.idxOf a,List.idxOf_lt_length_of_mem ha⟩
  let j : Fin xs.length := ⟨xs.idxOf b,List.idxOf_lt_length_of_mem hb⟩
  have ai : xs.get i=a := List.idxOf_get _
  have bj : xs.get j=b := List.idxOf_get _
  have forward : i<j := by
    rcases lt_trichotomy i j with yes|eqn|neg
    · exact yes
    · have same : a.val=b.val := congrArg Fin.val (ai.symm.trans ((congrArg xs.get eqn).trans bj))
      omega
    · have bad := ordered.rel_get_of_lt neg
      rw [bj,ai] at bad
      change b.val<a.val at bad
      omega
  change j.val=i.val+1
  by_contra gap
  have forward' : i.val<j.val := forward
  have jlt := j.isLt
  let mid : Fin xs.length := ⟨i.val+1,by omega⟩
  have low := ordered.rel_get_of_lt (show i < mid from by change i.val < i.val+1; omega)
  have high := ordered.rel_get_of_lt (show mid < j from by change i.val+1 < j.val; omega)
  rw [ai] at low
  rw [bj] at high
  change a.val<(xs.get mid).val at low
  change (xs.get mid).val<b.val at high
  omega

/-- Consecutive paired source bits stay consecutive in the receiving tick
even when earlier factor occurrences contribute other input or advice. -/
theorem Layout.slot_adjacent {a b : Fin S} (step : b.val=a.val+1) (own : P.origin a=P.origin b) :
    (P.slot b).val=(P.slot a).val+1 := by
  let f := P.origin a
  let t := P.owner f
  have inRow : f ∈ P.rows t := (P.owns f t).mpr rfl
  obtain ⟨pre,post,split⟩ := List.mem_iff_append.mp inRow
  rw [P.slot_prefix split (rfl : P.origin a=f), P.slot_prefix split (own.symm : P.origin b=f)]
  have sorted : (intervalBits P.origin f).Pairwise (· < ·) :=
    (List.pairwise_lt_finRange S).filter _
  have consecutive := adjacent_index _ sorted (mem_intervalBits.mpr rfl)
    (mem_intervalBits.mpr own.symm) step
  omega

end Hierarchy.FactorPinIntervals

end OAI
