import OAI.Optimization.LinearProgramming.PriceGame.PhasesTrace
import OAI.Optimization.LinearProgramming.PriceGame.PhasesSegment

/-! Canonical permanent identifiers for all representatives selected for the charging proof.
Two distinct skeletons have distinct IDs even if their numerical raw values are identical. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Phases
namespace Trace

open Learning

variable {N : ℕ} (r : Trace N) (hP : ∀ i, 1 ≤ r.truth i ∧ r.truth i ≤ (r.R : ℤ)+1)

/-- Select an actual position in the new batch. This choice is only used to analyze
the publicly computed catalogue; it is never an input to the trial algorithm. -/
noncomputable def expertId (first : ℕ) (s : Skeleton N) : ℕ :=
  (Pool.selected_has_persistent_id r.R s (seenProbes r.out) r.truth hP first).choose

theorem expertId_lookup {first t : ℕ} (ht : first ≤ t) (s : Skeleton N) :
    (replay (Pool.batch N r.R) (Population.start (Pool.batch N r.R)) r.out t).experts[r.expertId hP first s]? = some (r.chosen first s) := by
  rw [r.replay_catalog]
  exact (Pool.selected_has_persistent_id r.R s (seenProbes r.out) r.truth hP first).choose_spec
    (t+1) (Nat.lt_succ_of_le ht)

theorem expertId_mem {first t : ℕ} (ht : first ≤ t) (s : Skeleton N) :
    r.expertId hP first s ∈
      (replay (Pool.batch N r.R) (Population.start (Pool.batch N r.R)) r.out t).ids := by
  obtain ⟨hlt,_⟩ := List.getElem?_eq_some_iff.mp (r.expertId_lookup hP ht s)
  exact Finset.mem_range.mpr hlt

/-- Original equality of expert offsets forces equality of skeletons. -/
theorem expertId_injective (first : ℕ) : Function.Injective (r.expertId hP first) := by
  intro s u h
  have e₁ := r.expertId_lookup hP (t := first) (Nat.le_refl _) s
  have e₂ := r.expertId_lookup hP (t := first) (Nat.le_refl _) u
  rw [h] at e₁
  exact congrArg Expert.skeleton (Option.some.inj (e₁.symm.trans e₂))

/-- Numeric IDs and the representatives they denote are independent of the trial within
the same successful comparison interval. -/
theorem expertId_same_block {T : ℕ} (hR : 0 < r.R) {b : Fin (budget N r.R+1)}
    {u v : Fin T} (hu : r.trialTag T hR hP u = some b) (hv : r.trialTag T hR hP v = some b) :
    r.expertId hP (origin r.miss u) = r.expertId hP (origin r.miss v) := by
  rw [same_origin (miss := r.miss) (bound := r.exception_count T hR hP) hu hv]

/-- Interpret a concrete oracle game and a realized sequence of trial results as the trace
analyzed in Section 7. Raw priorities extend to inactive coordinates using their stored costs. -/
def fromHidden {R : ℕ} {a : Fin N} (h : Hidden N R a) (out : ℕ → RoundResult N) : Trace N :=
  ⟨R,h.positive,(fun i => (R : ℤ) + 1 - (h.cost i).val),out⟩

theorem fromHidden_box {R : ℕ} {a : Fin N} (h : Hidden N R a) (out : ℕ → RoundResult N)
    (i : Fin N) : 1 ≤ (fromHidden h out).truth i ∧ (fromHidden h out).truth i ≤ (R : ℤ)+1 := by
  have hc := (h.cost i).isLt
  dsimp [fromHidden]
  omega

/-- The same catalogue ID denotes the correctly predicting expert at every offset of a
nonempty block. The first membership supplies exactly the support needed for fixed sharing. -/
theorem segment_selection {T : ℕ} (hR : 0 < r.R) {b : Fin (budget N r.R+1)}
    (seg : Segment r.miss (r.exception_count T hR hP) b) (s : Skeleton N)
    (sgn : s.positive = r.positive) :
    let id := r.expertId hP seg.first s
    let e := r.chosen seg.first s
    let pop (u : ℕ) := replay (Pool.batch N r.R) (Population.start (Pool.batch N r.R)) r.out u
    id ∈ (pop seg.first).ids ∧ ∀ k < seg.length,
      (pop (seg.first.val+k)).experts[id]? = some e ∧
      ∀ q ∈ (r.out (seg.first.val+k)).observations.flatMap s.testsAt,
        compare (featureValue e.raw q.feature) q.threshold =
          compare (featureValue (fun i => (r.truth i : ℚ)) q.feature) q.threshold := by
  dsimp only
  refine ⟨r.expertId_mem hP le_rfl s, ?_⟩
  intro k hk
  have hfin := seg.finish_le
  let t : Fin T := ⟨seg.first.val+k, by omega⟩
  have ht := (seg.tick_iff t).mpr ⟨Nat.le_add_right .., Nat.add_lt_add_left hk seg.first.val⟩
  have he := (same_origin (bound := r.exception_count T hR hP) seg.good_first ht).symm.trans seg.origin_first
  refine ⟨r.expertId_lookup hP (Nat.le_add_right ..) s, ?_⟩
  intro q hq
  rw [← he]
  exact r.good_agrees t ((tag_some t b).mp ht).1 s sgn hq

end Trace
end Phases
end PriceGame
end LinearProgramming
end Optimization
end OAI
