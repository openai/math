import OAI.Optimization.LinearProgramming.Compression.Online
import OAI.Optimization.LinearProgramming.OracleSpec.Compression

/-! Relating the internal epoch state and the externally observable ordered response history. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.OracleSpec

variable {ι : Type} [DecidableEq ι]

/-- Emit each request with its response, in call order, keeping the internal generator state. -/
def serviceEventsFrom (request : MinorRequest ι) (st : RequestTrace ι) : List ι → List (ι × Option ℚ)
  | [] => []
  | u :: us => (u, request st.generators u) :: serviceEventsFrom request (st.step request u) us

theorem serviceEventsFrom_length (request : MinorRequest ι) (st : RequestTrace ι) (us : List ι) :
    (serviceEventsFrom request st us).length = us.length := by
  induction us generalizing st with
  | nil => rfl
  | cons u us ih => simp [serviceEventsFrom, ih]

theorem serviceEventsFrom_take (request : MinorRequest ι) (st : RequestTrace ι) (us : List ι) (j : ℕ) :
    (serviceEventsFrom request st us).take j = serviceEventsFrom request st (us.take j) := by
  induction us generalizing st j with
  | nil => simp [serviceEventsFrom]
  | cons u us ih => cases j <;> simp [serviceEventsFrom, ih]

/-- Only the newest consecutive sequence of successful answers survives a restart. -/
def epochAnswers : List (ι × Option ℚ) → List (ι × ℚ)
  | [] => []
  | (_, none) :: _ => []
  | (u, some q) :: rest => (u,q) :: epochAnswers rest

omit [DecidableEq ι] in
theorem agreesSinceRestart_iff_epochAnswers (f : ι → ℚ) (revHistory : List (ι × Option ℚ)) :
    MinorLog.agreesSinceRestart f revHistory ↔ ∀ u q, (u,q) ∈ epochAnswers revHistory → f u = q := by
  induction revHistory with
  | nil => simp [MinorLog.agreesSinceRestart, epochAnswers]
  | cons event rest ih =>
    rcases event with ⟨u, answer⟩
    cases answer with
    | none => simp [MinorLog.agreesSinceRestart, epochAnswers]
    | some q =>
      simp only [MinorLog.agreesSinceRestart, epochAnswers, ih, List.mem_cons]
      constructor
      · rintro ⟨hx, hr⟩ i c (pair | mem)
        · cases pair; exact hx
        · exact hr i c mem
      · intro h
        exact ⟨h u q (Or.inl rfl), fun i c mem ↦ h i c (Or.inr mem)⟩

private theorem serviceEventsFrom_epoch (request : MinorRequest ι) (st : RequestTrace ι) (us : List ι)
    (history : List (ι × Option ℚ)) (hst : epochAnswers history = st.replies) :
    epochAnswers ((serviceEventsFrom request st us).reverse ++ history) =
      (us.foldl (RequestTrace.step request) st).replies := by
  induction us generalizing st history with
  | nil => simpa [serviceEventsFrom] using hst
  | cons u us ih =>
    simp only [serviceEventsFrom, List.reverse_cons, List.append_assoc, List.singleton_append,
      List.foldl_cons]
    apply ih
    cases h : request st.generators u <;> simp [RequestTrace.step, h, epochAnswers, hst]

theorem serviceEvents_epoch (request : MinorRequest ι) (us : List ι) :
    epochAnswers (serviceEventsFrom request RequestTrace.start us).reverse =
      (RequestTrace.replay request us).replies := by
  simpa [RequestTrace.replay] using serviceEventsFrom_epoch request RequestTrace.start us [] rfl

theorem serviceEvents_restartCount (request : MinorRequest ι) (st : RequestTrace ι) (us : List ι) :
    (us.foldl (RequestTrace.step request) st).restarts =
      st.restarts + MinorLog.restartCount (serviceEventsFrom request st us) := by
  induction us generalizing st with
  | nil => simp [serviceEventsFrom, MinorLog.restartCount]
  | cons u us ih =>
    rw [List.foldl_cons, ih]
    cases h : request st.generators u <;>
      simp [serviceEventsFrom, RequestTrace.step, h, MinorLog.restartCount, Nat.add_assoc, Nat.add_comm]

/-- The local common-assignment proof at each generator set supplies the exact public
extension predicate for *every* response prefix, including an empty prefix or a final restart. -/
theorem serviceEvents_extensions (request : MinorRequest ι) (proxy logs : ι → ℝ)
    (htest : RestartTest proxy request) (n exponent : ℕ)
    (hlocal : ∀ J : Finset ι, IsDissociated proxy J → ∃ f : ι → ℚ,
      (∀ u, |(f u : ℝ)| ≤ (2 : ℝ)^exponent) ∧
      (∀ a : ι →₀ ℤ, a.sum (fun _ c => c.natAbs) ≤ 4 →
        |MinorLog.clip (MinorLog.threshold n) (a.sum (fun u c => (c : ℝ) * (f u : ℝ))) -
          MinorLog.clip (MinorLog.threshold n) (a.sum (fun u c => (c : ℝ) * logs u))| ≤
            (1/2 : ℝ)^(MinorLog.threshold n)) ∧
      ∀ u q, request J u = some q → f u = q)
    (us : List ι) (j : ℕ) :
    MinorLog.extension n exponent logs ((serviceEventsFrom request RequestTrace.start us).take j) := by
  let valid := fun f : ι → ℚ ↦ (∀ u, |(f u : ℝ)| ≤ (2 : ℝ)^exponent) ∧
      ∀ a : ι →₀ ℤ, a.sum (fun _ c => c.natAbs) ≤ 4 →
        |MinorLog.clip (MinorLog.threshold n) (a.sum (fun u c => (c : ℝ) * (f u : ℝ))) -
          MinorLog.clip (MinorLog.threshold n) (a.sum (fun u c => (c : ℝ) * logs u))| ≤
            (1/2 : ℝ)^(MinorLog.threshold n)
  obtain ⟨f, hf, agree⟩ := RequestTrace.common_assignment proxy request htest valid
    (fun J hJ ↦ by obtain ⟨f,hsize,hclip,hreq⟩ := hlocal J hJ; exact ⟨f, ⟨hsize,hclip⟩, hreq⟩)
    (us.take j)
  rw [serviceEventsFrom_take]
  refine ⟨f, ?_, hf⟩
  rw [agreesSinceRestart_iff_epochAnswers, serviceEvents_epoch]
  exact agree

end Compression
end LinearProgramming
end Optimization
end OAI
