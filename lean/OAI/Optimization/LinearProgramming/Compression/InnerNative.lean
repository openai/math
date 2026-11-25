import OAI.Optimization.LinearProgramming.Compression.InnerClock
import OAI.Optimization.LinearProgramming.BitRAM.HistoryMonotone
import OAI.Optimization.LinearProgramming.BitRAM.FragmentControl

/-! The RAM sign service may rely on the actual reachable ask format, including the prior
call count, and receives an explicit public dimension polynomial for the complete program. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
open OracleSpec

theorem machine_computes_for_clock (N g : ℕ) (hg : g≤paperWidth N) (member : Bool) (rank : ℕ)
    (hr : rank≤g) (hv : member=true → rank<g) (v : Fin (g+1) → ℝ) (neg : (Fin (g+1) → ℤ) → ℤ → Bool)
    (hn : ∀ a c, neg a c=true ↔ requestForm v a+c<0) (o : WordOracle) (ho : matchesCoordinates N v o) :
    let arg := inputWord N g member rank
    let value := sharedMinorStep N g (position g member rank) neg
    machine.ComputesWithin o arg (clock.eval N) (fun h w => w=outputWord value ∧ goodHistory N (g+2) h) ∧
      BitRAM.Dispatch.PermittedAsksFrom machine o
        (fun st _ => st.transcript.length<clock.eval N ∧ goodWord N (g+2) st.bufferRev.reverse) (machine.initial arg) ∧
      (outputWord value).length≤clock.eval N := by
  obtain ⟨run,len⟩ := machine_computes_trace_for N hg member rank hr hv v neg hn o ho
  refine ⟨run,?_,len⟩
  intro st j q next before hpc ask
  have h := BitRAM.permitted_of_transcript_post (good := fun e => goodWord N (g+2) e.1) run
    (fun _ _ p e he => p.2 e he) st j q next before hpc ask
  exact ⟨h.2,h.1⟩

theorem machine_computes_native_clock (N g : ℕ) (hg : g≤paperWidth N) (member : Bool) (rank : ℕ)
    (hr : rank≤g) (hv : member=true → rank<g) (mag : Fin (g+1) → ℚ) (hm : ∀ i,0 < mag i)
    (o : WordOracle) (ho : «matches» N mag o) :
    let arg := inputWord N g member rank
    let value := numericalValue N (position g member rank) mag
    machine.ComputesWithin o arg (clock.eval N) (fun h w => w=outputWord value ∧ goodHistory N (g+2) h) ∧
      BitRAM.Dispatch.PermittedAsksFrom machine o
        (fun st _ => st.transcript.length<clock.eval N ∧ goodWord N (g+2) st.bufferRev.reverse) (machine.initial arg) ∧
      (outputWord value).length≤clock.eval N := by
  let fuel := manuscriptProxyFuel N
  let p := paperRadius N+7
  exact machine_computes_for_clock N g hg member rank hr hv (generatorProxy fuel p mag)
    (requestMagnitudeNegative fuel p mag) (requestMagnitudeNegative_correct fuel p mag hm) o
    (matches_coordinates_of_magnitudes mag hm o ho)

theorem machine_computes_native : ∃ P : Polynomial ℕ, ∀ (N g : ℕ), g≤paperWidth N →
    ∀ (member : Bool) (rank : ℕ), rank≤g → (member=true → rank<g) →
    ∀ (mag : Fin (g+1) → ℚ), (∀ i,0 < mag i) → ∀ (o : WordOracle), «matches» N mag o →
    let arg := inputWord N g member rank
    let value := numericalValue N (position g member rank) mag
    machine.ComputesWithin o arg (P.eval N) (fun h w => w=outputWord value ∧ goodHistory N (g+2) h) ∧
      BitRAM.Dispatch.PermittedAsksFrom machine o
        (fun st _ => st.transcript.length<P.eval N ∧ goodWord N (g+2) st.bufferRev.reverse) (machine.initial arg) ∧
      (outputWord value).length≤P.eval N :=
  ⟨clock,machine_computes_native_clock⟩

end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
