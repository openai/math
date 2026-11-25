import OAI.Optimization.LinearProgramming.Compression.InnerSessionGraph

/-! A native sign-rounding session can be embedded either as the epoch phase, with one
zero field added to each ask, or as the request phase, with literally unchanged ask words. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
open OracleSpec ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open Lattice.Bit

private theorem roundWire (a : Round.Action) :
    wireView Driver.signPacket Driver.signPacket a = Round.wire a := by
  rcases a with z | ⟨row,c⟩ <;> rfl

theorem epochView (x : Input) (a : Round.Action) : routeEpoch x a=
    routeView (fun z => routeEpoch x (.inl z)) (fun r => Driver.signPacket (padRow r))
      (fun k : Driver.Carry => (Sum.inl (x,k) : Carry)) a := by
  rcases a with z|⟨r,k⟩ <;> rfl

theorem requestView (x : RequestContext) (a : Round.Action) : routeRequest x a=
    routeView (fun z => routeRequest x (.inl z)) Driver.signPacket
      (fun k : Driver.Carry => (Sum.inr (.inl (x,k)) : Carry)) a := by
  rcases a with z|⟨r,k⟩ <;> rfl

theorem liftEpoch (x : Input) (o : WordOracle) (past : Transcript) (E B rest : ℕ)
    (st : Driver.Input ⊕ (Word × Driver.Carry)) (z : Ints) (hist : Transcript) (k : ℕ)
    (sub : WordDialogue.Session Driver.inputCode Driver.carryCode (Driver.dispatch Driver.actualKernels)
      (oracleWith past epochWire o) E st [] (Driver.signPacket z) hist k)
    (hcarry : E+2*(inputCode x).length+4≤B) (answer : Word) (post : Transcript → Prop)
    (terminal : ∀ s : Input ⊕ (Word × Carry), dispatch s=routeEpoch x (.inl z) →
      (WordDialogue.stateCode inputEncoding carryCode s).length≤B → ∃ h n, n≤rest ∧
        WordDialogue.Session inputEncoding carryCode dispatch o B s (historyWith past epochWire hist) answer h n ∧ post h)
    (s : Input ⊕ (Word × Carry)) (hstart : dispatch s=routeEpoch x (Round.dispatch Driver.actualKernels st))
    (hs : (WordDialogue.stateCode inputEncoding carryCode s).length≤B) :
    ∃ h n, n≤k+rest ∧ WordDialogue.Session inputEncoding carryCode dispatch o B s past answer h n ∧ post h := by
  have H := transferSession (ei := Driver.inputCode) (ec := Driver.carryCode) (ej := inputEncoding) (ek := carryCode)
    (sub := Driver.dispatch Driver.actualKernels) (outer := dispatch) (Round.dispatch Driver.actualKernels) Driver.signPacket Driver.signPacket
    (fun t => (roundWire _).trans (Round.wire_dispatch _ t)) (fun z => routeEpoch x (.inl z)) (fun r => Driver.signPacket (padRow r))
    (fun c => Sum.inl (x,c)) epochWire epochWire_packet (fun w c => epochView x (Round.dispatch Driver.actualKernels (.inr (w,c))))
    past o post E B rest (by omega)
    (fun a h => (padRow_packet_length a).trans (by omega))
    (fun w c h => (epochCarry_size x w c).trans (by omega)) sub (by
      intro y h s hy hs
      have he := signPacket_injective h
      subst y
      exact terminal s hy hs)
    s (hstart.trans (epochView x _)) hs
  simpa [historyWith] using H

theorem liftRequest (x : RequestContext) (o : WordOracle) (past : Transcript) (R B rest : ℕ)
    (st : Driver.Input ⊕ (Word × Driver.Carry)) (z : Ints) (hist : Transcript) (k : ℕ)
    (sub : WordDialogue.Session Driver.inputCode Driver.carryCode (Driver.dispatch Driver.actualKernels)
      (oracleWith past id o) R st [] (Driver.signPacket z) hist k)
    (hcarry : R+2*(requestContextCode x).length+4≤B) (answer : Word) (post : Transcript → Prop)
    (terminal : ∀ s : Input ⊕ (Word × Carry), dispatch s=routeRequest x (.inl z) →
      (WordDialogue.stateCode inputEncoding carryCode s).length≤B → ∃ h n, n≤rest ∧
        WordDialogue.Session inputEncoding carryCode dispatch o B s (hist++past) answer h n ∧ post h)
    (s : Input ⊕ (Word × Carry)) (hstart : dispatch s=routeRequest x (Round.dispatch Driver.actualKernels st))
    (hs : (WordDialogue.stateCode inputEncoding carryCode s).length≤B) :
    ∃ h n, n≤k+rest ∧ WordDialogue.Session inputEncoding carryCode dispatch o B s past answer h n ∧ post h := by
  have H := transferSession (ei := Driver.inputCode) (ec := Driver.carryCode) (ej := inputEncoding) (ek := carryCode)
    (sub := Driver.dispatch Driver.actualKernels) (outer := dispatch) (Round.dispatch Driver.actualKernels) Driver.signPacket Driver.signPacket
    (fun t => (roundWire _).trans (Round.wire_dispatch _ t)) (fun z => routeRequest x (.inl z)) Driver.signPacket
    (fun c => Sum.inr (.inl (x,c))) id (fun _ => rfl) (fun w c => requestView x (Round.dispatch Driver.actualKernels (.inr (w,c))))
    past o post R B rest (by omega) (fun a h => by simpa using h.trans (by omega : R≤B))
    (fun w c h => (requestCarry_size x w c).trans (by omega)) sub (by
      intro y h s hy hs
      have he := signPacket_injective h
      subst y
      simpa [historyWith] using terminal s hy hs)
    s (hstart.trans (requestView x _)) hs
  simpa [historyWith] using H

end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
