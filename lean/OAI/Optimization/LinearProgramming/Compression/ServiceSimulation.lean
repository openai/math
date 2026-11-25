import OAI.Optimization.LinearProgramming.Compression.ServiceHistory

/-! Lifting the machine implementation of a single compression request to arbitrary
streams while the two mutable register files persist across calls. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
open OracleSpec.MinorLog

variable {ι : Type} [DecidableEq ι]

/-- Only the currently retained generators are required for the implementation invariant.
The caller's response history is used to state the guarantee and need not be stored. -/
theorem processes_from_single_step (request : MinorRequest ι) (encode : ι → List ℕ)
    (program : RAM.Program) (clock height outputBits : ℕ)
    (represents : Finset ι → RAM.State ℚ → Prop)
    (step : ∀ (J : Finset ι) (s : RAM.State ℚ), represents J s → ∀ u : ι,
      ∃ t, call program (clock-(encode u).length) height (resume s (encode u)) t ∧
        (encode u).length ≤ clock ∧ emits t (request J u) ∧
        (∀ q, request J u = some q → RAM.ratBits q ≤ outputBits) ∧
        represents (match request J u with | none => insert u J | some _ => J) t)
    (st : RequestTrace ι) (s : RAM.State ℚ) (hs : represents st.generators s) (us : List ι) :
    Processes encode program clock height outputBits s us (serviceEventsFrom request st us) := by
  induction us generalizing st s with
  | nil => exact .nil _
  | cons u us ih =>
    obtain ⟨t,ht,hclock,hemit,hsize,hnext⟩ := step st.generators s hs u
    have hrep : represents (st.step request u).generators t := by
      cases h : request st.generators u <;> simpa [RequestTrace.step,h] using hnext
    exact .cons ht hclock hemit hsize (ih _ t hrep)

end Compression
end LinearProgramming
end Optimization
end OAI
