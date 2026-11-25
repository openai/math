import OAI.Optimization.LinearProgramming.Lattice.BitRoundCodes
import OAI.Optimization.LinearProgramming.OracleSpec.WordDialogueDeployment
import OAI.Optimization.LinearProgramming.Lattice.BitRoundTrace

/-! Composition of single-probe executions with the repeated rounding controller and its
fixed physical word dialogue. Every transition records its actual continuation tape. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver

open OracleSpec

def wireHistory (reply : Word → Word) (steps : List Request) : Transcript :=
  (steps.map (fun x => (x.1,reply x.1))).reverse

def requestFits (L : ℕ) (reply : Word → Word) (q : Request) : Prop :=
  q.1.length ≤ L ∧ (reply q.1).length ≤ L ∧
    (WordDialogue.stateCode inputCode carryCode (.inr (reply q.1,q.2))).length ≤ L

/-- Transport a concrete bounded dialogue to the small-step word machine's session.
Its request count and entire transcript, including the answer words, are preserved. -/
theorem dialogueSession (f : Kernels) (o : WordOracle) (reply : Word → Word)
    {a steps out} (run : Dialogue f reply a steps out)
    (hr : ∀ history e, e ∈ steps → o history e.1 = reply e.1)
    (L : ℕ) (hout : out.length ≤ L) (hfit : ∀ q ∈ steps, requestFits L reply q)
    (s : Input ⊕ (Word × Carry)) (hs : dispatch f s = a)
    (hsize : (WordDialogue.stateCode inputCode carryCode s).length ≤ L) (history : Transcript) :
    WordDialogue.Session inputCode carryCode (dispatch f) o L s history out
      (wireHistory reply steps ++ history) (steps.length+1) := by
  induction run generalizing s history with
  | done w => simpa [wireHistory] using
      WordDialogue.Session.done (ei:=inputCode) (ec:=carryCode) (oracle:=o) (history:=history) hs hsize hout
  | @ask q c steps w rest ih =>
    obtain ⟨hpacket,hanswer,hstate⟩ := hfit (q,c) List.mem_cons_self
    have fit (e : Request) (he : e ∈ steps) := hfit e (List.mem_cons_of_mem _ he)
    have matchTail h (e : Request) (he : e ∈ steps) := hr h e (List.mem_cons_of_mem _ he)
    have answerMatch : o history q = reply q := hr history (q,c) List.mem_cons_self
    have sub := ih matchTail hout fit (.inr (reply q,c)) rfl hstate ((q,reply q)::history)
    have sub' : WordDialogue.Session inputCode carryCode (dispatch f) o L
        (.inr (o history q,c)) ((q,o history q)::history) w
        (wireHistory reply steps ++ (q,reply q)::history) (steps.length+1) := by
      simpa only [answerMatch] using sub
    have total := WordDialogue.Session.query hs hsize hpacket
      (show (o history q).length ≤ L by simpa only [answerMatch] using hanswer) sub'
    simpa [wireHistory,List.append_assoc] using total

end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
