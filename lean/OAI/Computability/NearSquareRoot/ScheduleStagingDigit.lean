import OAI.Computability.NearSquareRoot.ScheduleStagingOffer
import OAI.Computability.NearSquareRoot.ScheduleStagingCall
import OAI.Computability.NearSquareRoot.ScheduleStagingPrivate

/-!
# The reusable physical digit stage

The stage moves the raw query to the dedicated input, runs the four-letter
machine on just the active tapes, and restores the private bank. The output
is left directly at the correct absolute top of the controller register.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingDigit

open IntegerMultiplication TM CommonAlphabet CommonAlphabet.Pipeline StagingPorts Bits

variable {J I Q X : Type} [DecidableEq J] [DecidableEq X] [Fintype I]

abbrev PC (Q I : Type) := (StagingCopy.Phase ⊕ Q) ⊕ (Option I → Reset.Phase)

def start : PC Q I := .inl (.inl .start)
def stop : PC Q I := .inr fun _ => .done

def rule (one : J) (e : Encoding X) (s : X) (hs : ∀ a, s ≠ e.embed a)
    (m : Rule Public.Letter Q (Index I)) (q : Q) : Rule (StagingReset.Symbol X) (PC Q I) (Bank J I) :=
  let first := StagingOffer.rule (I:=I) one e s hs
  let second := StagingCall.rule one e m
  let clear := StagingPrivate.working_rule J I (e.embed none)
  TapeSequence.rule (TapeSequence.rule first second q) clear (fun _ => .seekLeft)

theorem run (one : J) (e : Encoding X) (s : X) (hmark : ∀ a, s ≠ e.embed a)
    (m : Rule Public.Letter Q (Index I)) (q : Q) (shelf : J → Tape X)
    (x y ans : Word) {u t R S : ℕ} {z : Config Public.Letter Q (Index I)}
    (hx : x.length = u) (hy : y.length = u)
    (hist : Trace (advance m) ⟨q,publicLoad x y⟩ t z) (halt : advance m z = none)
    (result : z.tape (.inl true) = Tape.loaded none (ans.map Public.bit))
    (space : VisitsAtMost m ⟨q,publicLoad x y⟩ t S)
    (hquery : shelf one = StagingOffer.queryTape e u x y)
    (guard : 6*u+7 ≤ R) (room : S+2*u ≤ R)
    (hs : ∀ j, -(R:ℤ) ≤ (shelf j).pos ∧ (shelf j).pos ≤ R) :
    let bank := StagingOffer.blankBank (I:=I) e
    let answer := imageTape e.embed (-(2*u:ℤ)) (Tape.loaded none (ans.map Public.bit))
    let prog := rule one e s hmark m q
    let done : Config _ (PC Q I) _ := ⟨stop,marked R (Function.update shelf one answer) bank⟩
    ∃ n ≤ 4*u+t+5*R+11,
      FencedRun prog (fun _ => -(R:ℤ)) (fun _ => (R:ℤ)) ⟨start,marked R shelf bank⟩ n done ∧
      advance prog done = none := by
  let offer := StagingOffer.rule (I:=I) one e s hmark
  let core := StagingCall.rule one e m
  let clear := StagingPrivate.working_rule J I (e.embed none)
  let mid := TapeSequence.rule offer core q
  let blank := StagingOffer.blankBank (I:=I) e
  let reply := imageTape e.embed (-(2*u:ℤ)) (Tape.loaded none (ans.map Public.bit))
  let store := Function.update shelf one reply
  obtain ⟨prep,hprep⟩ := StagingOffer.run (I:=I) one e s hmark shelf hx hy hquery guard hs
  obtain ⟨call,hcall⟩ := StagingCall.run one e m q R S (-(2*u:ℤ)) shelf x y ans hist halt
    result space (by omega) (by omega) (by omega) hs
  rw [← StagingOffer.output_eq_call (I:=I) one e R u shelf x y] at call
  have merged := TapeSequence.run_fenced offer core q prep hprep call
  have hmerged := (TapeSequence.run offer core q prep.1 hprep call.1 hcall).2
  obtain ⟨hp,hout⟩ := StagingPrivate.active_clean e m q x y hist space (by omega : S ≤ R)
    (by simp [rawWord,hx,hy]; omega : (rawWord x y).length ≤ R)
  obtain ⟨k,hk,wipe,hwipe,freeze⟩ :=
    StagingPrivate.reset (e.embed none) R store (active e z.tape) hp hout
  have hf : FencedRun clear (fun _ => -(R:ℤ)) (fun _ => (R:ℤ))
      ⟨(fun _ => Reset.Phase.seekLeft),marked R store (active e z.tape)⟩ k
      ⟨(fun _ => Reset.Phase.done),marked R store blank⟩ := by
    refine ⟨wipe,?_⟩
    intro i hi z cut j
    obtain ⟨unchanged,confined⟩ := freeze hi cut
    rcases j with j|j
    · rw [unchanged]
      change -(R:ℤ) ≤ (store j).pos ∧ (store j).pos ≤ R
      by_cases eq : j=one
      · subst j
        simp only [store,Function.update_self]
        change -(R:ℤ) ≤ -(2*u:ℤ)+0 ∧ -(2*u:ℤ)+0 ≤ (R:ℤ)
        omega
      · simpa only [store,Function.update_of_ne eq] using hs j
    · exact confined j
  have all := TapeSequence.run_fenced mid clear (fun _ => .seekLeft) merged hmerged hf
  have stopped := (TapeSequence.run mid clear (fun _ => .seekLeft) merged.1 hmerged hf.1 hwipe).2
  refine ⟨_,?_,all,stopped⟩
  omega

end StagingDigit

end NearSquareRoot
end Computability
end OAI
