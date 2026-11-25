import OAI.Optimization.LinearProgramming.Compression.InnerSessionRound

/-! Compose the measured rounding and graph sessions in the controller's chronological
order, including the early return on a stored generator. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
open OracleSpec ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open Lattice.Bit

theorem assembleSessions (x : Input) (o : WordOracle) (zE zR : Ints) (gout : Graph.Out)
    (E R G ke kr kg : ℕ) (he hr hg : Transcript)
    (epoch : WordDialogue.Session Driver.inputCode Driver.carryCode (Driver.dispatch Driver.actualKernels)
      (oracleWith [] epochWire o) E (.inl (epochInput x)) [] (Driver.signPacket zE) he ke)
    (req : WordDialogue.Session Driver.inputCode Driver.carryCode (Driver.dispatch Driver.actualKernels)
      (oracleWith (historyWith [] epochWire he) id o) R (.inl (requestInput x)) [] (Driver.signPacket zR) hr kr)
    (graph : WordDialogue.Session RequestTable.inputCode RequestTable.Dialogue.carryCode RequestTable.graphRequestDispatch
      (oracleWith (hr++historyWith [] epochWire he) id o) G (.inl (paperGrid x.1.1,normalizeRow zR)) []
      (RequestTable.Dialogue.outputCode gout) hg kg) :
    let gamma := normalizeRow zE
    let result := combinedAnswer x gamma gout
    let B := sessionSize x gamma E R G result
    let eh := historyWith [] epochWire he
    ∃ final cnt, cnt≤ke+kr+kg+1 ∧ WordDialogue.Session inputEncoding carryCode dispatch o B (.inl x) []
      (outputWord result) final cnt ∧ final=(if x.2.1 then eh else hg++(hr++eh)) := by
  intro gamma result B eh
  have eBound : E+2*(inputCode x).length+4≤B := by dsimp [B,sessionSize]; omega
  have rBound : R+2*(requestContextCode (x,gamma)).length+4≤B := by dsimp [B,sessionSize]; omega
  have gBound : G+2*(Projector.rowCode gamma).length+4≤B := by dsimp [B,sessionSize]; omega
  have outBound : (outputWord result).length≤B := by dsimp [B,sessionSize]; omega
  have startBound : (WordDialogue.stateCode inputEncoding carryCode (.inl x)).length≤B := by
    dsimp [B,sessionSize,WordDialogue.stateCode]; omega
  by_cases mem : x.2.1=true
  · have hval : result=some (readAt 0 gamma x.2.2) := by simp [result,combinedAnswer,mem]
    have pose : routeEpoch x (.inl zE)=.inl (outputWord result) := by simp [routeEpoch,hval,mem,gamma]
    obtain ⟨f,c,hc,run,last⟩ := liftEpoch x o [] E B 1 (.inl (epochInput x)) zE he ke epoch eBound
      (outputWord result) (fun f => f=eh) (by
        intro s step hlen
        exact ⟨eh,1,by decide,WordDialogue.Session.done (step.trans pose) hlen outBound,rfl⟩)
      (.inl x) rfl startBound
    exact ⟨f,c,by omega,run,by simpa [mem] using last⟩
  · have hnot : x.2.1=false := Bool.eq_false_iff.mpr mem
    have hval : result=affineResult gamma gout := by simp [result,combinedAnswer,hnot]
    have pose : routeEpoch x (.inl zE)=routeRequest (x,gamma) (Round.dispatch Driver.actualKernels (.inl (requestInput x))) := by
      simp [routeEpoch,hnot,gamma]
    have graphTerminal (s : Input ⊕ (Word × Carry)) (step : dispatch s=routeRequest (x,gamma) (.inl zR))
        (hlen : (WordDialogue.stateCode inputEncoding carryCode s).length≤B) :
        ∃ f c, c≤kg+1 ∧ WordDialogue.Session inputEncoding carryCode dispatch o B s (hr++eh) (outputWord result) f c ∧
          f=hg++(hr++eh) := by
      rw [hval]
      apply liftGraph o (hr++eh) G B gamma gout (.inl (paperGrid x.1.1,normalizeRow zR)) hg kg graph gBound
        (by simpa only [← hval] using outBound) s _ hlen
      exact step
    have next (s : Input ⊕ (Word × Carry)) (step : dispatch s=routeEpoch x (.inl zE))
        (hlen : (WordDialogue.stateCode inputEncoding carryCode s).length≤B) :
        ∃ f c, c≤kr+(kg+1) ∧ WordDialogue.Session inputEncoding carryCode dispatch o B s eh (outputWord result) f c ∧
          f=hg++(hr++eh) :=
      liftRequest (x,gamma) o eh R B (kg+1) (.inl (requestInput x)) zR hr kr req rBound
        (outputWord result) (fun f => f=hg++(hr++eh)) graphTerminal s (step.trans pose) hlen
    obtain ⟨f,c,hc,run,last⟩ := liftEpoch x o [] E B (kr+(kg+1)) (.inl (epochInput x)) zE he ke epoch
      eBound (outputWord result) (fun f => f=hg++(hr++eh)) next (.inl x) rfl startBound
    exact ⟨f,c,by omega,run,by simpa [hnot] using last⟩

end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
