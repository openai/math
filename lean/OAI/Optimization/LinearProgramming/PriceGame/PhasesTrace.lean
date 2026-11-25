import OAI.Optimization.LinearProgramming.PriceGame.Phases
import OAI.Optimization.LinearProgramming.PriceGame.PhasesOrder
import OAI.Optimization.LinearProgramming.PriceGame.LearningReset
import OAI.Optimization.LinearProgramming.PriceGame.Schedule

/-! The greedy exception analysis of §7 on the actual recorded probes of the trial loop.
The selections and exceptions here depend on the hidden assignment only in the proof. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Phases

open Learning

variable {N : ℕ}

/-- Inputs to the analysis of one concrete transcript. Every probe and its ancestors
come from the output of the corresponding executed trial. -/
structure Trace (N : ℕ) where
  R : ℕ
  positive : Bool
  truth : Fin N → ℤ
  out : ℕ → RoundResult N

namespace Trace

variable (r : Trace N)

def chosen (first : ℕ) (s : Skeleton N) : Expert N :=
  Pool.selectedExpert r.R s (seenProbes r.out first) r.truth

def disagrees (first : ℕ) (s : Skeleton N) (q : Test N) : Bool :=
  decide (compare (featureValue (r.chosen first s).raw q.feature) q.threshold ≠
    compare (featureValue (fun i => (r.truth i : ℚ)) q.feature) q.threshold)

/-- Inspect the actual observed comparisons on every skeleton of the hidden sign. -/
def miss (first t : ℕ) : Bool :=
  (Skeleton.enumerate N).any fun s =>
    (s.positive == r.positive) &&
      ((r.out t).observations.flatMap s.testsAt).any (r.disagrees first s)

theorem miss_iff (first t : ℕ) :
    r.miss first t = true ↔
      ∃ s : Skeleton N, s.positive = r.positive ∧
      ∃ q ∈ (r.out t).observations.flatMap s.testsAt,
        compare (featureValue (r.chosen first s).raw q.feature) q.threshold ≠
          compare (featureValue (fun i => (r.truth i : ℚ)) q.feature) q.threshold := by
  simp only [miss, List.any_eq_true, Skeleton.mem_enumerate, Bool.and_eq_true, beq_iff_eq, true_and, disagrees, decide_eq_true_eq]

private theorem history_mono {u v : ℕ} (h : u ≤ v) :
    seenProbes r.out u ⊆ seenProbes r.out v := by
  induction v, h using Nat.le_induction with
  | base => exact fun _ hh => hh
  | succ v _ ih =>
    intro p hp
    exact List.mem_append_left _ (ih hp)

private theorem origin_at_epoch (T k : ℕ) (hk : k ≤ (events r.miss T).card) :
    origin r.miss (epochStart (events r.miss T) k) = epochStart (events r.miss T) k := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [epochStart_succ _ _ (by omega), origin_succ]
    have he := (mem_events.mp (eventAt_mem (events r.miss T) ⟨k,by omega⟩)).2
    rw [he]
    rfl

theorem origin_at_exception (T : ℕ) (k : Fin (events r.miss T).card) :
    origin r.miss (eventAt (events r.miss T) k) = epochStart (events r.miss T) k := by
  let s := events r.miss T
  have ht := (mem_events.mp (eventAt_mem s k)).1
  apply (origin_const r.miss (epochStart_le_event s k) ?_).trans (r.origin_at_epoch T k k.isLt.le)
  intro u hu hv
  by_cases he : exceptional r.miss u = true
  · exact False.elim ((not_mem_between_events s k hu hv) (mem_events.mpr ⟨hv.trans ht,he⟩))
  · simpa using he

/-- The source's bound on the number of switches. Its exponent is independent of the trial count. -/
def budget (N R : ℕ) : ℕ := (Skeleton.enumerate N).length * 66^2 * (1 + 66 * (1 + R.size))

theorem exception_count (T : ℕ) (hR : 0 < r.R)
    (hP : ∀ i, 1 ≤ r.truth i ∧ r.truth i ≤ (r.R : ℤ)+1) :
    (events r.miss T).card ≤ budget N r.R := by
  let s := events r.miss T
  let hist (k : ℕ) := seenProbes r.out (epochStart s k)
  apply Reset.number_of_changes r.R s.card hR r.truth hP hist
  · intro k _
    apply r.history_mono
    exact epochStart_mono s (Nat.le_succ _)
  · intro k hk
    let j : Fin s.card := ⟨k,hk⟩
    let t := eventAt s j
    have he : r.miss (origin r.miss t) t = true := (mem_events.mp (eventAt_mem s j)).2
    obtain ⟨sk,_,q,hq,hwrong⟩ := (r.miss_iff _ t).mp he
    use sk, q
    constructor
    · obtain ⟨p,hp,hq'⟩ := List.mem_flatMap.mp hq
      have hp' : p ∈ hist (k+1) := by
        dsimp only [hist]
        rw [epochStart_succ s k hk]
        exact List.mem_append_right _ hp
      exact List.mem_flatMap.mpr ⟨p,hp',hq'⟩
    · have hb := r.origin_at_exception T j
      change origin r.miss t = epochStart s k at hb
      rw [hb] at hwrong
      exact hwrong

/-- The same tag has the exact finite codomain used by the majority proof. -/
def trialTag (T : ℕ) (hR : 0 < r.R) (hP : ∀ i, 1 ≤ r.truth i ∧ r.truth i ≤ (r.R : ℤ)+1) :
    Fin T → Option (Fin (budget N r.R + 1)) :=
  tag r.miss T (budget N r.R) (r.exception_count T hR hP)

theorem trialTag_exception_bound (T : ℕ) (hR : 0 < r.R)
    (hP : ∀ i, 1 ≤ r.truth i ∧ r.truth i ≤ (r.R : ℤ)+1) :
    (Finset.univ.filter fun t => r.trialTag T hR hP t = none).card ≤ budget N r.R :=
  (exceptional_fiber (r.exception_count T hR hP)).trans_le (r.exception_count T hR hP)

theorem good_agrees (t : ℕ) (good : exceptional r.miss t = false) (s : Skeleton N)
    (sign : s.positive = r.positive) {q : Test N} (hq : q ∈ (r.out t).observations.flatMap s.testsAt) :
    compare (featureValue (r.chosen (origin r.miss t) s).raw q.feature) q.threshold =
      compare (featureValue (fun i => (r.truth i : ℚ)) q.feature) q.threshold := by
  by_contra h
  have bad := (r.miss_iff _ t).mpr ⟨s,sign,q,hq,h⟩
  change exceptional r.miss t = true at bad
  rw [good] at bad
  contradiction

/-- The root schedule's current ordered list is exactly the catalogue through this trial. -/
theorem replay_catalog (t : ℕ) :
    (replay (Pool.batch N r.R) (Population.start (Pool.batch N r.R)) r.out t).experts =
      Catalog.entries (fun u => Pool.batch N r.R (seenProbes r.out u)) (t+1) := by
  rw [replay_entries]
  induction t with
  | zero => simp [expectedEntries, Catalog.entries, seenProbes]
  | succ t ih => rw [expectedEntries, Catalog.entries, ih]

/-- Each selected skeleton uses one permanent ID for the entire good interval. This ID is
already present when the interval starts, even if distinct trials produce identical experts. -/
theorem stable_block_selection (T : ℕ) (hR : 0 < r.R)
    (hP : ∀ i, 1 ≤ r.truth i ∧ r.truth i ≤ (r.R : ℤ)+1)
    (b : Fin (budget N r.R + 1)) (u : Fin T) (hu : r.trialTag T hR hP u = some b)
    (s : Skeleton N) (sign : s.positive = r.positive) :
    let first := origin r.miss u
    let chosen := r.chosen first s
    let entries (t : ℕ) :=
      (replay (Pool.batch N r.R) (Population.start (Pool.batch N r.R)) r.out t).experts
    ∃ id : ℕ, (entries first)[id]? = some chosen ∧
      ∀ t : Fin T, r.trialTag T hR hP t = some b →
        (entries t)[id]? = some chosen ∧
        ∀ q ∈ (r.out t).observations.flatMap s.testsAt,
          compare (featureValue chosen.raw q.feature) q.threshold =
            compare (featureValue (fun i => (r.truth i : ℚ)) q.feature) q.threshold := by
  dsimp only
  obtain ⟨id,hi⟩ := Pool.selected_has_persistent_id r.R s (seenProbes r.out) r.truth hP
    (origin r.miss u)
  refine ⟨id, ?_, ?_⟩
  · rw [r.replay_catalog]
    exact hi _ (Nat.lt_succ_self _)
  · intro t ht
    have he := same_origin (miss := r.miss) (bound := r.exception_count T hR hP) hu ht
    refine ⟨?_, ?_⟩
    · rw [r.replay_catalog]
      apply hi
      rw [he]
      exact Nat.lt_succ_of_le (origin_le r.miss t)
    · intro q hq
      rw [he]
      exact r.good_agrees t ((tag_some t b).mp ht).1 s sign hq

end Trace
end Phases
end PriceGame
end LinearProgramming
end Optimization
end OAI
