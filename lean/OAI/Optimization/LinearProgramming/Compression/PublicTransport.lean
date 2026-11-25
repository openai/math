import OAI.Optimization.LinearProgramming.Compression.ServiceHistory
import OAI.Optimization.LinearProgramming.Compression.RequestIndex
import OAI.Optimization.LinearProgramming.Compression.AdaptiveRequests

/-! Transporting the completed epoch and its comparisons through the public permutation of minor indices. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators
open OAI.Optimization.LinearProgramming.OracleSpec

/-- Execute the very same policy after mapping the requested index and the current generators. -/
def pullbackMinorRequest {α β : Type} (e : α ≃ β) (req : MinorRequest β) : MinorRequest α :=
  fun J u ↦ req (J.map e.toEmbedding) (e u)

theorem RestartTest.pullback {α β : Type} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) {proxy : β → ℝ} {req : MinorRequest β} (h : RestartTest proxy req) :
    RestartTest (fun u ↦ proxy (e u)) (pullbackMinorRequest e req) where
  fresh := by
    intro J u hJ hr hu
    have hd := (isDissociated_map_iff proxy e.toEmbedding J).mpr hJ
    exact h.fresh _ _ hd hr (Finset.mem_map.mpr ⟨u,hu,rfl⟩)
  independent := by
    intro J u hJ hr
    apply (isDissociated_map_iff proxy e.toEmbedding (insert u J)).mp
    rw [Finset.map_insert]
    exact h.independent _ _ ((isDissociated_map_iff proxy e.toEmbedding J).mpr hJ) hr

/-- A bounded comparison on the public finitely supported representation is the matching
comparison on the finite internal type, including zero and cancellations. -/
theorem validMinorAssignment_pullback {α β : Type} [Fintype β]
    (e : α ≃ β) {n : ℕ} {f : β → ℚ} {logs : β → ℝ} (h : ValidMinorAssignment n logs f) :
    (∀ i, |(f (e i) : ℝ)| ≤ (2 : ℝ)^(onlineMinorBitPolynomial.eval n)) ∧
    ∀ a : α →₀ ℤ, a.sum (fun _ c ↦ c.natAbs) ≤ 4 →
      |MinorLog.clip (MinorLog.threshold n) (a.sum (fun i c ↦ (c : ℝ) * (f (e i) : ℝ))) -
        MinorLog.clip (MinorLog.threshold n) (a.sum (fun i c ↦ (c : ℝ) * logs (e i)))| ≤
        (1 / 2 : ℝ)^(MinorLog.threshold n) := by
  classical
  let : Fintype α := Fintype.ofEquiv _ e.symm
  refine ⟨fun i ↦ by exact_mod_cast (h.1 (e i)).1, ?_⟩
  intro a ha
  have habs : (∑ j, |(a (e.symm j) : ℝ)|) ≤ 4 := by
    rw [e.symm.sum_comp (fun i ↦ |(a i : ℝ)|)]
    have hnat : ∑ i, (a i).natAbs ≤ 4 := by simpa [Finsupp.sum_fintype] using ha
    have hcast : (∑ i, |(a i : ℝ)|) = ((∑ i, (a i).natAbs : ℕ) : ℝ) := by
      push_cast; simp only [Nat.cast_natAbs, Int.cast_abs]
    rw [hcast]; exact_mod_cast hnat
  have transport (g : β → ℝ) : intForm (fun j ↦ a (e.symm j)) g =
      a.sum (fun i c ↦ (c : ℝ) * g (e i)) := by
    rw [a.sum_fintype (fun i c ↦ (c : ℝ) * g (e i)) (fun _ ↦ by simp)]
    unfold intForm
    simpa only [Equiv.symm_apply_apply] using
      (e.sum_comp (fun j ↦ (a (e.symm j) : ℝ) * g j)).symm
  have hh := h.2 (fun j ↦ a (e.symm j)) habs
  rw [transport, transport] at hh
  simpa only [MinorLog.threshold, MinorLog.clip, paperRadius, clip, one_div, inv_pow] using hh

/-- A successful answer, including one from an earlier epoch, has bounded reduced encoding. -/
theorem serviceEventsFrom_outputBits {ι : Type} [DecidableEq ι] {req : MinorRequest ι}
    {proxy : ι → ℝ} (h : RestartTest proxy req) (B : ℕ)
    (hb : ∀ J, IsDissociated proxy J → ∀ u q, req J u = some q → RAM.ratBits q ≤ B)
    (st : RequestTrace ι) (hs : IsDissociated proxy st.generators) (us : List ι) :
    ∀ u q, (u,some q) ∈ serviceEventsFrom req st us → RAM.ratBits q ≤ B := by
  induction us generalizing st with
  | nil => simp [serviceEventsFrom]
  | cons v vs ih =>
    intro u q hm
    simp only [serviceEventsFrom, List.mem_cons] at hm
    rcases hm with hfirst | hrest
    · have : u = v := congrArg Prod.fst hfirst
      subst u
      apply hb _ hs v q
      exact (congrArg Prod.snd hfirst).symm
    · apply ih _ _ u q hrest
      cases hi : req st.generators v with
      | none => simpa [RequestTrace.step, hi] using h.independent _ _ hs hi
      | some v' => simpa [RequestTrace.step, hi] using hs

/-- Chronological response indices are exactly the submitted indices. -/
theorem serviceEventsFrom_indices {ι : Type} [DecidableEq ι] (req : MinorRequest ι)
    (st : RequestTrace ι) (us : List ι) : (serviceEventsFrom req st us).map Prod.fst = us := by
  induction us generalizing st with
  | nil => rfl
  | cons u us ih => simp [serviceEventsFrom, ih]

end Compression
end LinearProgramming
end Optimization
end OAI
