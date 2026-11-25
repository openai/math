import OAI.Optimization.LinearProgramming.Compression.ServiceSimulation

/-! Lift a one-call representation of the generator set on the fixed RAM to every
public response stream, preserving one representation across restarts and answers. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.OracleSpec

/-- Only the current generator set is persistent simulation state. The proof's old answer
history need not be stored in the RAM. -/
theorem serviceEventsFrom_processes {ι : Type} [DecidableEq ι]
    (encode : ι → List ℕ) (program : RAM.Program) (clock height outputBits : ℕ)
    (proxy : ι → ℝ) (request : MinorRequest ι) (hrequest : RestartTest proxy request)
    (rep : Finset ι → RAM.State ℚ → Prop)
    (hwords : ∀ i, (encode i).length ≤ clock)
    (hsize : ∀ J, IsDissociated proxy J → ∀ u q, request J u = some q → RAM.ratBits q ≤ outputBits)
    (hstep : ∀ J s u, IsDissociated proxy J → rep J s → ∃ t : RAM.State ℚ,
      MinorLog.call program (clock-(encode u).length) height (MinorLog.resume s (encode u)) t ∧
      MinorLog.emits t (request J u) ∧ rep (if (request J u).isNone then insert u J else J) t)
    (us : List ι) (st : RequestTrace ι) (s : RAM.State ℚ)
    (hJ : IsDissociated proxy st.generators) (hs : rep st.generators s) :
    MinorLog.Processes encode program clock height outputBits s us (serviceEventsFrom request st us) := by
  apply processes_from_single_step request encode program clock height outputBits
    (fun J st ↦ IsDissociated proxy J ∧ rep J st) _ st s ⟨hJ,hs⟩ us
  rintro J m ⟨hd,hm⟩ u
  obtain ⟨t,call,emit,next⟩ := hstep J m u hd hm
  refine ⟨t, call, hwords u, emit, hsize _ hd u, ?_⟩
  cases he : request J u with
  | none => exact ⟨hrequest.independent _ _ hd he, by simpa [he] using next⟩
  | some q => exact ⟨hd, by simpa [he] using next⟩

end Compression
end LinearProgramming
end Optimization
end OAI
