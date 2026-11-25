import OAI.Optimization.LinearProgramming.Compression.Basic
import OAI.Optimization.LinearProgramming.Compression.SeparationBasic
import Mathlib.Data.Finset.Card

/-! Restart and transcript invariants for the on-demand minor procedure in §3.
The reply list models the observer's transcript since the last restart. Only the generator set
is passed to the request procedure. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

variable {ι : Type*} [DecidableEq ι]

/-- `none` requests a restart and adds the requested minor to the generator list. -/
abbrev MinorRequest (ι : Type*) := Finset ι → ι → Option ℚ

structure RequestTrace (ι : Type*) where
  generators : Finset ι
  restarts : ℕ
  replies : List (ι × ℚ)

def RequestTrace.start : RequestTrace ι := ⟨∅, 0, []⟩

def RequestTrace.step (request : MinorRequest ι) (st : RequestTrace ι) (u : ι) : RequestTrace ι :=
  match request st.generators u with
  | none => ⟨insert u st.generators, st.restarts + 1, []⟩
  | some q => {st with replies := (u, q) :: st.replies}

/-- Replay a transcript of requested indices, including any adaptively selected prefix. -/
def RequestTrace.replay (request : MinorRequest ι) (indices : List ι) : RequestTrace ι :=
  indices.foldl (RequestTrace.step request) RequestTrace.start

/-- This condition concerns only the elementary insertion test, independently of how the
caller selects its queries or uses the answers. -/
structure RestartTest (proxy : ι → ℝ) (request : MinorRequest ι) : Prop where
  fresh : ∀ J u, IsDissociated proxy J → request J u = none → u ∉ J
  independent : ∀ J u, IsDissociated proxy J → request J u = none →
    IsDissociated proxy (insert u J)

theorem RequestTrace.replay_invariants (proxy : ι → ℝ) (request : MinorRequest ι)
    (htest : RestartTest proxy request) (indices : List ι) :
    let st := RequestTrace.replay request indices
    IsDissociated proxy st.generators ∧ st.generators.card = st.restarts ∧
      ∀ u q, (u, q) ∈ st.replies → request st.generators u = some q := by
  let invariant := fun st : RequestTrace ι =>
    IsDissociated proxy st.generators ∧ st.generators.card = st.restarts ∧
      ∀ u q, (u, q) ∈ st.replies → request st.generators u = some q
  have starting : invariant RequestTrace.start := by
    refine ⟨?_, rfl, by simp [RequestTrace.start]⟩
    intro A hA B hB hne
    change A ⊆ ∅ at hA
    change B ⊆ ∅ at hB
    exact (hne ((Finset.subset_empty.mp hA).trans (Finset.subset_empty.mp hB).symm)).elim
  have one_step (st : RequestTrace ι) (u : ι) (hs : invariant st) :
      invariant (st.step request u) := by
    obtain ⟨hJ, hcard, hlog⟩ := hs
    cases he : request st.generators u with
    | none =>
      have hu := htest.fresh _ _ hJ he
      exact ⟨by simpa [RequestTrace.step, he] using htest.independent _ _ hJ he,
        by simp [RequestTrace.step, he, Finset.card_insert_of_notMem hu, hcard],
        by simp [RequestTrace.step, he]⟩
    | some q =>
      refine ⟨by simpa [RequestTrace.step, he] using hJ,
        by simpa [RequestTrace.step, he] using hcard, ?_⟩
      intro v r hvr
      simp only [RequestTrace.step, he, List.mem_cons, Prod.mk.injEq] at hvr
      simp only [RequestTrace.step, he]
      rcases hvr with ⟨rfl, rfl⟩ | ht
      · exact he
      · exact hlog _ _ ht
  have fold (qs : List ι) (st : RequestTrace ι) (hs : invariant st) :
      invariant (qs.foldl (RequestTrace.step request) st) := by
    induction qs generalizing st with
    | nil => exact hs
    | cons u us ih => exact ih _ (one_step _ _ hs)
  exact fold _ _ starting

/-- A run with arbitrarily many successful requests restarts only as often as the maximum
possible cardinality of a dissociated family. The bound also covers every incomplete prefix. -/
theorem RequestTrace.restarts_le (proxy : ι → ℝ) (request : MinorRequest ι)
    (htest : RestartTest proxy request) (bound : ℝ)
    (hbound : ∀ J : Finset ι, IsDissociated proxy J → (J.card : ℝ) ≤ bound)
    (indices : List ι) : ((RequestTrace.replay request indices).restarts : ℝ) ≤ bound := by
  obtain ⟨hJ, hcard, _⟩ := RequestTrace.replay_invariants proxy request htest indices
  rw [← hcard]
  exact hbound _ hJ

/-- A single complete assignment valid for all successful requests at each fixed generator
set is simultaneously valid for every reply of the current run. -/
theorem RequestTrace.common_assignment (proxy : ι → ℝ) (request : MinorRequest ι)
    (htest : RestartTest proxy request) (valid : (ι → ℚ) → Prop)
    (hlocal : ∀ J : Finset ι, IsDissociated proxy J →
      ∃ f : ι → ℚ, valid f ∧ ∀ u q, request J u = some q → f u = q)
    (indices : List ι) :
    ∃ f : ι → ℚ, valid f ∧ ∀ u q, (u, q) ∈ (RequestTrace.replay request indices).replies →
      f u = q := by
  obtain ⟨hJ, _, hlog⟩ := RequestTrace.replay_invariants proxy request htest indices
  obtain ⟨f, hf, h⟩ := hlocal _ hJ
  exact ⟨f, hf, fun u q huq => h _ _ (hlog u q huq)⟩

end Compression
end LinearProgramming
end Optimization
end OAI
