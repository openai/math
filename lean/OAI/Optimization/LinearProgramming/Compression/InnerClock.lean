import OAI.Optimization.LinearProgramming.Compression.InnerNativeSemantics
import OAI.Optimization.LinearProgramming.Compression.InnerMachine
import OAI.Optimization.LinearProgramming.Compression.InnerCostEnvelope
import OAI.Optimization.LinearProgramming.Compression.InnerParameterSize

/-! A fixed polynomial clock for the complete finite service, independent of matrix data
and of the sizes of the original rational minors. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
open OracleSpec _root_.OAI.Optimization.LinearProgramming.Lattice Lattice.Bit ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open Polynomial

noncomputable def graphWidthPolynomial : Polynomial ℕ := RequestTable.Dialogue.dispatchWidthPoly RequestTable.prepareP
noncomputable def graphCountPolynomial : Polynomial ℕ := RequestTable.Dialogue.depthPoly RequestTable.prepareP+1
noncomputable def commonWidthPolynomial : Polynomial ℕ := Cost.words parameterPolynomial Driver.frameBound normalizedBound
  graphWidthPolynomial returnBound RequestTable.paperInputPolynomial
noncomputable def commonCountPolynomial : Polynomial ℕ := Cost.rounds parameterPolynomial countPolynomial
  graphCountPolynomial RequestTable.paperInputPolynomial
noncomputable def clock : Polynomial ℕ :=
  Cost.dispatcherTime dispatchP.shared.bound commonCountPolynomial commonWidthPolynomial+commonWidthPolynomial

/-- The source machine halts with the exact requested rational and a fully typed bounded
query transcript. The same dimension polynomial bounds the length of the returned word. -/
theorem machine_computes_trace_for {g : ℕ} (N : ℕ) (hg : g≤paperWidth N) (member : Bool) (rank : ℕ) (hr : rank≤g)
    (hv : member=true → rank<g) (v : Fin (g+1) → ℝ) (neg : (Fin (g+1) → ℤ) → ℤ → Bool)
    (hn : ∀ a c, neg a c=true ↔ requestForm v a+c<0) (o : WordOracle) (ho : matchesCoordinates N v o) :
    let ans := sharedMinorStep N g (position g member rank) neg
    machine.ComputesWithin o (inputWord N g member rank) (clock.eval N)
      (fun hist w => w=outputWord ans ∧ goodHistory N (g+2) hist) ∧ (outputWord ans).length≤clock.eval N := by
  intro ans
  let x : Input := ((N,g),member,rank)
  let gamma := List.ofFn (sharedEpochCommit N g neg)
  let B := sessionSize x gamma (epochFrame N g) (requestFrame g) (graphFrame N) ans
  let s : Cost.Sizes := ⟨epochFrame N g,requestFrame g,graphFrame N,(inputEncoding x).length,(inputCode x).length,
    (requestContextCode (x,gamma)).length,(Projector.rowCode gamma).length,(outputWord ans).length,
    roundCount (g+1) (epochRadius N g),roundCount (g+2) (requestRadius g),graphCount N⟩
  obtain ⟨hist,cnt,session,ct,typed,hgamma,hout⟩ := native_session_for N hg member rank hv v neg hn o ho
  obtain ⟨hi,hj,he,hr'⟩ := parameterSizes N g rank member hg hr
  have stages : Cost.Stages s N parameterPolynomial Driver.frameBound countPolynomial normalizedBound
      graphWidthPolynomial graphCountPolynomial returnBound RequestTable.paperInputPolynomial := by
    refine ⟨hi,hj,Procedure.eval_nat_mono _ he,Procedure.eval_nat_mono _ hr',?_,le_rfl,?_,hout,
      parameterRoundCount _ _ _ he,parameterRoundCount _ _ _ hr',?_⟩
    · exact hgamma.trans (Procedure.eval_nat_mono normalizedBound (Procedure.eval_nat_mono _ he))
    · simp [s,requestContextCode,prodCode,pairBits_length]
    · simp [s,graphCount,graphCountPolynomial]
  have time := Cost.stage_time_le dispatchP.shared.bound cnt B stages ct (le_rfl : B ≤ s.buffer)
  have words := (Cost.stages_common stages).output
  have clockValue : clock.eval N =
      (Cost.dispatcherTime dispatchP.shared.bound commonCountPolynomial commonWidthPolynomial).eval N +
        commonWidthPolynomial.eval N := by
    unfold clock
    exact Polynomial.eval_add
  have baseTime : cnt*(dispatchP.shared.bound.eval B+18*B+18)+3 ≤
      (Cost.dispatcherTime dispatchP.shared.bound commonCountPolynomial commonWidthPolynomial).eval N := by
    dsimp only [commonCountPolynomial,commonWidthPolynomial]
    exact time
  have time' : cnt*(dispatchP.shared.bound.eval B+18*B+18)+3≤clock.eval N := by
    rw [clockValue]
    exact baseTime.trans (Nat.le_add_right _ _)
  have out' : (outputWord ans).length≤clock.eval N := by
    rw [clockValue]
    exact words.trans (Nat.le_add_left _ _)
  obtain ⟨t,c,run,ht,halt,eqhist,eqout⟩ := machine_of_session o session
  exact ⟨⟨t,c,run,ht.trans time',halt,eqout,by simpa only [eqhist] using typed⟩,out'⟩

theorem machine_computes_trace {g : ℕ} (N : ℕ) (hg : g≤paperWidth N) (member : Bool) (rank : ℕ) (hr : rank≤g)
    (hv : member=true → rank<g) (mag : Fin (g+1) → ℚ) (hm : ∀ i,0 < mag i) (o : WordOracle) (ho : «matches» N mag o) :
    let ans := numericalValue N (position g member rank) mag
    machine.ComputesWithin o (inputWord N g member rank) (clock.eval N)
      (fun hist w => w=outputWord ans ∧ goodHistory N (g+2) hist) ∧ (outputWord ans).length≤clock.eval N := by
  let fuel := manuscriptProxyFuel N
  let p := paperRadius N+7
  exact machine_computes_trace_for N hg member rank hr hv (generatorProxy fuel p mag)
    (requestMagnitudeNegative fuel p mag) (requestMagnitudeNegative_correct fuel p mag hm) o
    (matches_coordinates_of_magnitudes mag hm o ho)

end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
