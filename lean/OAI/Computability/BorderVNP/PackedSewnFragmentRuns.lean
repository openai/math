import OAI.Computability.BorderVNP.FiniteSewnFieldRunCount
import Mathlib.Data.List.Chain

/-! # Sparse endpoint characterization of the canonical exterior sewing runs

An ordered stream of contiguous fragments represents the partial predecessor-to-source
map. Its positive maximal blocks have exactly the endpoints of the canonical lane
definition. No lane-wise gate circuit is involved in the comparison.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment

open scoped Classical
open private start slope runStart interval start_le start_mono from OAI.Computability.BorderVNP.FiniteSewnFieldRuns
open private start_eq_of_constant from OAI.Computability.BorderVNP.FiniteSewnFieldRunCount

/-- Chronological coverage of a suffix by contiguous intervals, with all starts and ends in bounds. -/
def Partition (limit : ℕ) : ℕ → List Interval → Prop
  | k, [] => k = limit
  | k, p::tail => p.oldStart = k ∧ p.oldStart+p.width ≤ limit ∧ Partition limit (p.oldStart+p.width) tail

/-- A fragment reads consecutive source lanes or clamps its entire predecessor interval to zero. -/
def Good {old next : ℕ} (read : Fin old → Option (Fin next)) (p : Interval) : Prop :=
  ∀ i < p.width, ∀ k : Fin old, k.val = p.oldStart+i →
    (read k).map Fin.val = p.source.map (·+i)

/-- The constant translation of an interval, or the unique zero-clamp label. -/
def label (p : Interval) := p.source.map (fun u => (u : ℤ)-p.oldStart)

/-- Consecutive nonempty fragments have the same label exactly when the latter starts at the
next source lane of the former, including two adjacent zero clamps. -/
theorem label_eq_iff (p q : Interval) (atNext : q.oldStart = p.oldStart+p.width) :
    label p = label q ↔ p.source.map (·+p.width) = q.source := by
  cases hp : p.source <;> cases hq : q.source <;> simp [label,hp,hq,atNext]
  omega

variable {old next : ℕ} (read : Fin old → Option (Fin next))

private theorem lane_label {p : Interval} (good : Good read p) (k : Fin old)
    (lo : p.oldStart ≤ k.val) (hi : k.val < p.oldStart+p.width) : slope read k.val = label p := by
  have h := good (k.val-p.oldStart) (by omega) k (Nat.add_sub_of_le lo).symm
  change (if h : k.val < old then (read ⟨k.val,h⟩).map (fun j => (j.val : ℤ)-k.val) else none) =
    p.source.map (fun j => (j : ℤ)-p.oldStart)
  rw [dite_eq_left k.isLt]
  cases a : read k <;> cases b : p.source <;> simp_all
  omega

/-- Canonical ends in the suffix beginning at the supplied predecessor lane. -/
private def endsFrom (atLane : ℕ) : Finset (Fin old) :=
  Finset.univ.filter fun k => atLane ≤ k.val ∧ ∀ j : Fin old, runStart read j = runStart read k → j ≤ k

private theorem ext_interval {p q : Interval} (a : p.oldStart=q.oldStart) (b : p.width=q.width)
    (c : p.source=q.source) : p=q := by
  cases p; cases q; simp_all

private theorem canon_suffix (runs : List Interval) (atLane : ℕ) (tiles : Partition old atLane runs)
    (positive : ∀ p ∈ runs, 0 < p.width) (good : ∀ p ∈ runs, Good read p)
    (separate : runs.IsChain (fun p q => label p ≠ label q))
    (first : atLane < old → start (slope read) atLane = atLane) :
    ((endsFrom read atLane).sort.map (interval read)) = runs := by
  induction runs generalizing atLane with
  | nil =>
    have h : endsFrom read atLane = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      have low := (Finset.mem_filter.mp hk).2.1
      change atLane=old at tiles
      omega
    simp [h]
  | cons p tail ih =>
    obtain ⟨hp,cap,tiled⟩ := tiles
    subst atLane
    have pw := positive p List.mem_cons_self
    let f : Fin old := ⟨p.oldStart,by omega⟩
    let z : Fin old := ⟨p.oldStart+p.width-1,by omega⟩
    have zlo : p.oldStart ≤ z.val := by dsimp [z]; omega
    have zhi : z.val < p.oldStart+p.width := by dsimp [z]; omega
    have zend : z.val+1 = p.oldStart+p.width := by dsimp [z]; omega
    have gp := good p List.mem_cons_self
    have key (k : Fin old) (lo : p.oldStart ≤ k.val) (hi : k.val < p.oldStart+p.width) :
        runStart read k = f := by
      apply Fin.ext
      change start (slope read) k.val = p.oldStart
      apply (start_eq_of_constant (slope read) p.oldStart k.val lo ?_).trans (first f.isLt)
      intro j low high
      let u : Fin old := ⟨j,high.trans_lt k.isLt⟩
      exact (lane_label read gp u low (high.trans_lt hi)).trans
        (lane_label read gp f le_rfl (by dsimp [f]; omega)).symm
    have zk := key z zlo zhi
    have fresh (h : p.oldStart+p.width < old) : start (slope read) (p.oldStart+p.width) = p.oldStart+p.width := by
      cases tail with
      | nil => change p.oldStart+p.width = old at tiled; omega
      | cons q rs =>
        obtain ⟨atNext,qcap,_⟩ := tiled
        have qw := positive q (List.mem_cons_of_mem p List.mem_cons_self)
        have distinct := (List.isChain_cons_cons.mp separate).1
        let j : Fin old := ⟨p.oldStart+p.width,h⟩
        have right := lane_label read (good q (List.mem_cons_of_mem p List.mem_cons_self)) j
          (by change q.oldStart ≤ p.oldStart+p.width; omega)
          (by change p.oldStart+p.width < q.oldStart+q.width; omega)
        have different : slope read (z.val+1) ≠ slope read z.val := by
          rw [zend,show slope read (p.oldStart+p.width)=label q from right,lane_label read gp z zlo zhi]
          exact Ne.symm distinct
        rw [←zend,start,ite_eq_right different]
    have last (j : Fin old) (hj : runStart read j = runStart read z) : j ≤ z := by
      by_contra hn
      have large : p.oldStart+p.width ≤ j.val := by change ¬ j.val ≤ z.val at hn; omega
      have past := start_mono (slope read) large
      rw [fresh (large.trans_lt j.isLt)] at past
      have hkey : start (slope read) j.val = p.oldStart := congrArg Fin.val (hj.trans zk)
      omega
    have union : endsFrom read p.oldStart = insert z (endsFrom read (p.oldStart+p.width)) := by
      ext k
      simp only [endsFrom,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
      constructor
      · rintro ⟨low,atEnd⟩
        by_cases high : p.oldStart+p.width ≤ k.val
        · exact .inr ⟨high,atEnd⟩
        · have stop := atEnd z (zk.trans (key k low (by omega)).symm)
          exact .inl (Fin.ext (by change z.val ≤ k.val at stop; omega))
      · rintro (rfl|⟨high,atEnd⟩)
        · exact ⟨zlo,last⟩
        · exact ⟨by omega,atEnd⟩
    have sorted : (endsFrom read p.oldStart).sort = z :: (endsFrom read (p.oldStart+p.width)).sort := by
      rw [union]
      apply Finset.sort_insert
      · intro k hk
        exact zhi.le.trans (Finset.mem_filter.mp hk).2.1
      · intro hz
        exact Nat.not_le_of_lt zhi (Finset.mem_filter.mp hz).2.1
    have desc : interval read z = p := by
      have src := gp 0 pw f (by simp [f])
      rw [interval,zk]
      apply ext_interval
      · rfl
      · change z.val+1-p.oldStart = p.width; omega
      · cases H : p.source <;> simpa [H] using src
    rw [sorted,List.map_cons,desc]
    exact congrArg (p :: ·) (ih _ tiled (fun u hu => positive u (List.mem_cons_of_mem p hu))
      (fun u hu => good u (List.mem_cons_of_mem p hu)) separate.tail fresh)

/-- A positive chronological partition with different adjacent translations is exactly the
canonical ordered interval list of the actual lane map. Empty predecessors yield the empty list. -/
theorem canonical_of_partition (runs : List Interval) (tiles : Partition old 0 runs)
    (positive : ∀ p ∈ runs, 0 < p.width) (good : ∀ p ∈ runs, Good read p)
    (separate : runs.IsChain (fun p q => label p ≠ label q)) :
    runs = intervals read := by
  have e : endsFrom read 0 = Finset.univ.filter
      (fun k : Fin old => ∀ j : Fin old, runStart read j = runStart read k → j ≤ k) := by
    ext k; simp [endsFrom]
  rw [←canon_suffix read runs 0 tiles positive good separate (fun _ => rfl),e,intervals]

end Packing.SewnField.Fragment

end BorderVNP
end Computability
end OAI
