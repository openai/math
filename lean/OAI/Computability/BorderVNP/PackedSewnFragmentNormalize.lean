import OAI.Computability.BorderVNP.PackedSewnFragmentRuns

/-! # Coalescing compatible fragments in one physical site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment

open scoped Classical

/-- Site-local action of one sparse predecessor record on the already compacted suffix. -/
def prependRun (p : Interval) : List Interval → List Interval
  | [] => [p]
  | q::qs => if p.oldStart+p.width = q.oldStart ∧ p.source.map (·+p.width) = q.source then
      ⟨p.oldStart,p.width+q.width,p.source⟩ :: qs else p::q::qs

/-- Chronological interval list obtained by merging only adjacent continuing words. -/
def localRuns (xs : List Interval) := xs.foldr prependRun []

variable {old next : ℕ} (read : Fin old → Option (Fin next))

/-- Joining two continuing descriptors retains their entire partial lane map. -/
private theorem join_good {p q : Interval} (pg : Good read p) (qg : Good read q)
    (atNext : p.oldStart+p.width = q.oldStart) (src : p.source.map (·+p.width) = q.source) :
    Good read ⟨p.oldStart,p.width+q.width,p.source⟩ := by
  intro i hi k hval
  change i < p.width+q.width at hi
  change k.val = p.oldStart+i at hval
  by_cases pre : i < p.width
  · exact pg i pre k hval
  · have h := qg (i-p.width) (by omega) k (by omega)
    change (read k).map Fin.val = p.source.map (·+i)
    rw [←src] at h
    cases a : p.source <;> simp only [a,Option.map_none,Option.map_some] at h ⊢
    · exact h
    · exact h.trans (congrArg some (by omega))

private structure Maximal (k : ℕ) (runs : List Interval) : Prop where
  tiles : Partition old k runs
  positive : ∀ p ∈ runs, 0 < p.width
  good : ∀ p ∈ runs, Good read p
  separate : runs.IsChain (fun p q => label p ≠ label q)

private theorem prepend_maximal (p : Interval) (tail : List Interval)
    (room : p.oldStart+p.width ≤ old) (positive : 0 < p.width) (pg : Good read p)
    (h : Maximal read (p.oldStart+p.width) tail) :
    Maximal read p.oldStart (prependRun p tail) := by
  cases tail with
  | nil =>
    exact ⟨⟨rfl,room,h.tiles⟩,by simpa [prependRun] using positive,by simpa [prependRun] using pg,List.isChain_singleton _⟩
  | cons q qs =>
    obtain ⟨loc,qroom,tiled⟩ := h.tiles
    have qw := h.positive q List.mem_cons_self
    have qg := h.good q List.mem_cons_self
    by_cases comp : p.oldStart+p.width=q.oldStart ∧ p.source.map (·+p.width)=q.source
    · rw [prependRun,ite_eq_left comp]
      let r := (⟨p.oldStart,p.width+q.width,p.source⟩ : Interval)
      have endEq : r.oldStart+r.width = q.oldStart+q.width := by dsimp [r]; omega
      have rg := join_good read pg qg comp.1 comp.2
      have labelEq : label r = label q := (label_eq_iff p q loc).2 comp.2
      refine ⟨⟨rfl,endEq ▸ qroom,endEq ▸ tiled⟩,?_,?_,?_⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl|hz
        · change 0 < p.width+q.width; omega
        · exact h.positive z (List.mem_cons_of_mem q hz)
      · intro z hz
        rcases List.mem_cons.mp hz with rfl|hz
        · exact rg
        · exact h.good z (List.mem_cons_of_mem q hz)
      · cases qs with
        | nil => exact List.isChain_singleton _
        | cons a rest =>
          have chain := List.isChain_cons_cons.mp h.separate
          exact List.isChain_cons_cons.mpr ⟨labelEq ▸ chain.1,chain.2⟩
    · rw [prependRun,ite_eq_right comp]
      refine ⟨⟨rfl,room,h.tiles⟩,?_,?_,List.isChain_cons_cons.mpr ⟨?_,h.separate⟩⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl|hz
        · exact positive
        · exact h.positive z hz
      · intro z hz
        rcases List.mem_cons.mp hz with rfl|hz
        · exact pg
        · exact h.good z hz
      · exact fun eqn => comp ⟨loc.symm,(label_eq_iff p q loc).mp eqn⟩

private theorem normalize_maximal (xs : List Interval) (k : ℕ) (tiles : Partition old k xs)
    (positive : ∀ p ∈ xs, 0<p.width) (good : ∀ p ∈ xs, Good read p) :
    Maximal read k (localRuns xs) := by
  induction xs generalizing k with
  | nil => exact ⟨tiles,by simp [localRuns],by simp [localRuns],List.isChain_nil⟩
  | cons p ps ih =>
    obtain ⟨loc,room,rest⟩ := tiles
    subst k
    exact prepend_maximal read p (localRuns ps) room (positive p List.mem_cons_self) (good p List.mem_cons_self)
      (ih _ rest (fun q hq => positive q (List.mem_cons_of_mem p hq)) (fun q hq => good q (List.mem_cons_of_mem p hq)))

/-- The site-local sparse merge returns exactly the canonical ordered zero and equality intervals. -/
theorem localRuns_eq (xs : List Interval) (tiles : Partition old 0 xs)
    (positive : ∀ p ∈ xs, 0 < p.width) (good : ∀ p ∈ xs, Good read p) :
    localRuns xs = intervals read := by
  have h := normalize_maximal read xs 0 tiles positive good
  exact canonical_of_partition read _ h.tiles h.positive h.good h.separate

/-- Dropping width-zero reservations preserves the exact starting positions and coverage.
This includes a zero-size predecessor and any number of consecutive empty slots. -/
theorem Partition.filter_positive (xs : List Interval) (k : ℕ) (h : Partition old k xs) :
    Partition old k (xs.filter fun p => decide (0<p.width)) := by
  induction xs generalizing k with
  | nil => exact h
  | cons p ps ih =>
    obtain ⟨loc,room,rest⟩ := h
    by_cases pos : 0<p.width
    · simp only [List.filter_cons,decide_eq_true pos,ite_true]
      exact ⟨loc,room,ih _ rest⟩
    · have eqn : p.oldStart+p.width=k := by omega
      simp only [List.filter_cons,decide_eq_false pos,Bool.false_eq_true,ite_false]
      exact eqn ▸ ih _ rest

/-- For an unfiltered physical directory, first remove the empty slots. The positive
fragments then merge to the canonical rows even if two continuations surrounded empty slots. -/
theorem filter_localRuns_eq (xs : List Interval) (tiles : Partition old 0 xs)
    (good : ∀ p ∈ xs, Good read p) : localRuns (xs.filter (fun p => decide (0<p.width))) = intervals read :=
  localRuns_eq read _ (Partition.filter_positive _ _ tiles)
    (fun _ h => of_decide_eq_true (List.mem_filter.mp h).2)
    (fun p h => good p (List.mem_filter.mp h).1)

end Packing.SewnField.Fragment

end BorderVNP
end Computability
end OAI
