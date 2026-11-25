import OAI.Optimization.LinearProgramming.PriceGame.ControlReplayMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlEncodingPad

/-! Convert a completed replay to a public dialogue action.  The suspended
continuation keeps the original reverse reply tape and public header. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native
namespace Replay

open ExactQuantumFactoring.BitStackProgram Procedure
open OracleSpec
open OAI.Optimization.LinearProgramming.PriceGame.Control.Wire (packedQueryCode)

/-- The tagged initial input or reply already has exactly the cells of the updated tape. -/
noncomputable def inputTapeP :
    Procedure (Dialogue.inputCode eiPad ecPad) ecPad startTape :=
  ((identity ecPad).precompose startTape).congrEncoding
    (fun e => (inputCode_pad e).symm) (fun _ => rfl)

/-- Encode the external price request in the order used by the public oracle. -/
def queryPacket (q : PackedQuery) : Word :=
  encodeNat q.index ++ q.prices.flatMap encodeRat

@[simp] theorem queryPacket_pack {N : ℕ} (q : Query N) :
    queryPacket (packQuery q) = priceQuery q.index q.prices := rfl

noncomputable def queryPacketP : Procedure packedQueryCode id queryPacket :=
  ((OracleSpec.Wire.writeQuery.comp (swap (listCode ratCode) Nat.bits)).precompose
    (fun q : PackedQuery => (q.prices,q.index))).congrFun (by intro _; rfl)

/-- A finished sign requires one output bit.  An unserved request carries the full
tape that was supplied before any of the replay steps consumed its local copy. -/
def boxTerminal (t : Tape) : Bool ⊕ PackedQuery → Bool ⊕ (Word × Tape)
  | .inl b => .inl b
  | .inr q => .inr (queryPacket q,t)

/-- A complete source computation may leave an unused tail of replies.  The public
terminal action keeps only its bit, or the first unanswered packed query. -/
def terminalResult {N : ℕ} : (Bool × List Bool) ⊕ Query N → Bool ⊕ PackedQuery :=
  Sum.map Prod.fst packQuery

theorem box_observeTape (solver : PublicSolver) (t : Tape) :
    boxTerminal t (terminalResult (observe (solver t.input) t.reverseReplies.reverse)) =
      observeTape solver t := by
  unfold observeTape
  cases observe (solver t.input) t.reverseReplies.reverse <;> rfl

theorem box_observe_dispatch (solver : PublicSolver) (event : PublicInput ⊕ (Bool × Tape)) :
    let t := startTape event
    boxTerminal t (terminalResult (observe (solver t.input) t.reverseReplies.reverse)) =
      dispatch solver event :=
  box_observeTape solver (startTape event)

noncomputable def boxTerminalP : Procedure (prodCode ecPad stoppedCode)
    (Dialogue.actionCode ecPad) (fun z => boxTerminal z.1 z.2) := by
  let halt : Procedure boolCode (Dialogue.actionCode ecPad)
      (Sum.inl : Bool → Bool ⊕ (Word × Tape)) :=
    (prepend boolCode [false]).result (by intro _; rfl)
  let query : Procedure (prodCode id ecPad) (Dialogue.actionCode ecPad)
      (Sum.inr : Word × Tape → Bool ⊕ (Word × Tape)) :=
    (prepend (prodCode id ecPad) [true]).result (by
      rintro ⟨packet,t⟩
      change true :: (quoteBits packet ++ ecPad t) = true :: (frame packet ++ ecPad t)
      rw [quoteBits_eq_frame])
  let finish := halt.comp (second ecPad boolCode)
  let request := query.comp ((queryPacketP.comp (second ecPad packedQueryCode)).pair
    (first ecPad packedQueryCode))
  exact (Join.contextCases false default finish request).congrFun
    (by rintro ⟨t,b|q⟩ <;> rfl)

/-- The chosen fallback makes extraction total.  A stopped replay returns its exact
value, as used in the complete-run and short-prefix correctness statements. -/
def stoppedOutput : State → Bool ⊕ PackedQuery :=
  Sum.elim (fun _ => .inl false) id

noncomputable def stoppedOutputP : Procedure stateCode stoppedCode stoppedOutput :=
  casesSum (constant runningCode stoppedCode (Sum.inl false)) (identity stoppedCode)

@[simp] theorem stoppedOutput_stopped (out : Bool ⊕ PackedQuery) :
    stoppedOutput (.inr out) = out := rfl

noncomputable def boxReplayP : Procedure (prodCode ecPad stateCode) (Dialogue.actionCode ecPad)
    (fun z => boxTerminal z.1 (stoppedOutput z.2)) :=
  boxTerminalP.comp ((first ecPad stateCode).pair (stoppedOutputP.comp (second ecPad stateCode)))

@[simp] theorem boxReplay_done (t : Tape) (b : Bool) :
    boxTerminal t (stoppedOutput (done b)) = .inl b := rfl

@[simp] theorem boxReplay_pending (t : Tape) {N : ℕ} (q : Query N) :
    boxTerminal t (stoppedOutput (pending (packQuery q))) = .inr (priceQuery q.index q.prices, t) := rfl

/-- Compose a replay routine with the physical input and output encoders.  The
saved tape takes a separate wire through the replay and is used unchanged on suspension. -/
noncomputable def dialogueOfReplay (solver : PublicSolver) {run : Tape → State}
    (runP : Procedure ecPad stateCode run)
    (exactRun : ∀ t, run t = .inr (terminalResult (observe (solver t.input) t.reverseReplies.reverse))) :
    Procedure (Dialogue.inputCode eiPad ecPad) (Dialogue.actionCode ecPad) (dispatch solver) := by
  let finish := boxReplayP.comp ((identity ecPad).pair runP)
  apply (finish.comp inputTapeP).congrFun
  intro event
  let t := startTape event
  change boxTerminal t (stoppedOutput (run t)) = dispatch solver event
  rw [exactRun,stoppedOutput_stopped]
  exact box_observe_dispatch solver event

end Replay
end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
