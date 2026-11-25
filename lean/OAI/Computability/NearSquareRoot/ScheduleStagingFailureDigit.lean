import OAI.Computability.NearSquareRoot.ScheduleStagingDigit

/-! # A short multiplication either returns its true answer or crosses a fence -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingDigit

open IntegerMultiplication TM CommonAlphabet CommonAlphabet.Pipeline StagingPorts Bits

variable {J I Q X : Type} [DecidableEq J] [DecidableEq X] [Fintype I]

theorem run_or_overflow (one : J) (e : Encoding X) (s : X) (hmark : ∀ a, s ≠ e.embed a)
    (m : Rule Public.Letter Q (Index I)) (q : Q) (shelf : J → Tape X)
    (x y ans : Word) {u t R : ℕ} {z : Config Public.Letter Q (Index I)}
    (hx : x.length = u) (hy : y.length = u)
    (hist : Trace (advance m) ⟨q,publicLoad x y⟩ t z) (halt : advance m z = none)
    (result : z.tape (.inl true) = Tape.loaded none (ans.map Public.bit))
    (hquery : shelf one = StagingOffer.queryTape e u x y)
    (guard : 6*u+7 ≤ R)
    (hs : ∀ j, -(R:ℤ) ≤ (shelf j).pos ∧ (shelf j).pos ≤ R) :
    let bank := StagingOffer.blankBank (I:=I) e
    let answer := imageTape e.embed (-(2*u:ℤ)) (Tape.loaded none (ans.map Public.bit))
    let prog := rule one e s hmark m q
    let done : Config _ (PC Q I) _ := ⟨stop,marked R (Function.update shelf one answer) bank⟩
    (∃ n ≤ 4*u+t+5*R+11,
      FencedRun prog (fun _ => -(R:ℤ)) (fun _ => (R:ℤ)) ⟨start,marked R shelf bank⟩ n done ∧
      advance prog done = none ) ∨
    ∃ k z j, Trace (advance prog) ⟨start,marked R shelf bank⟩ k z ∧
      ((z.tape j).pos < -(R:ℤ) ∨ (R:ℤ) < (z.tape j).pos) := by
  classical
  let offer := StagingOffer.rule (I:=I) one e s hmark
  let core := StagingCall.rule one e m
  let clear := StagingPrivate.working_rule J I (e.embed none)
  let mid := TapeSequence.rule offer core q
  let blank := StagingOffer.blankBank (I:=I) e
  let reply := imageTape e.embed (-(2*u:ℤ)) (Tape.loaded none (ans.map Public.bit))
  let store := Function.update shelf one reply
  obtain ⟨prep,hprep⟩ := StagingOffer.run (I:=I) one e s hmark shelf hx hy hquery guard hs
  let first := marked R (Function.update shelf one (StagingOffer.replyTape e u))
    (StagingOffer.privateBankInput (I:=I) e x y)
  let last := marked R store (active e z.tape)
  obtain ⟨call,hcall⟩ := StagingCall.raw one e m q R (-(2*u:ℤ)) shelf x y ans hist halt result
  rw [← StagingOffer.output_eq_call (I:=I) one e R u shelf x y] at call
  change Trace (advance core) ⟨q,first⟩ t ⟨z.pc,last⟩ at call
  by_cases bounded : ∀ v ≤ t, ∀ w, Trace (advance core) ⟨q,first⟩ v w → ∀ j,
      -(R:ℤ) ≤ (w.tape j).pos ∧ (w.tape j).pos ≤ R
  · left
    have confined : FencedRun core (fun _ => -(R:ℤ)) (fun _ => (R:ℤ))
        ⟨q,first⟩ t ⟨z.pc,last⟩ := ⟨call,bounded⟩
    have merged := TapeSequence.run_fenced offer core q prep hprep confined
    have hmerged := (TapeSequence.run offer core q prep.1 hprep call hcall).2
    have hp (i : Option I) : -(R:ℤ) ≤ (active e z.tape i).pos ∧ (active e z.tape i).pos ≤ R :=
      bounded t le_rfl _ call (.inr i)
    have hout (i : Option I) (a : ℤ) (ha : a < -(R:ℤ) ∨ (R:ℤ) < a) :
        (active e z.tape i).absolute a = e.embed none := by
      have eq := StagingReset.outside_eq_of_confined core R call (fun hv ht => bounded _ hv _ ht)
        (.inr i) a ha
      change (StagingReset.markedTape R (active e z.tape i)).absolute a =
        (StagingReset.markedTape R (StagingOffer.privateBankInput e x y i)).absolute a at eq
      rw [StagingReset.markedTape_absolute,StagingReset.markedTape_absolute] at eq
      have h := congrArg (fun b : StagingReset.Symbol X => b.1.1) eq
      change (active e z.tape i).absolute a = (StagingOffer.privateBankInput e x y i).absolute a at h
      rw [h,StagingOffer.privateBankInput_active]
      cases i with
      | none =>
        have empty := StagingPrivate.loaded_outside (rawWord x y) (by simp [rawWord,hx,hy]; omega : (rawWord x y).length ≤ R) a ha
        simpa [active,imageTape,Tape.absolute,publicLoad,Pipeline.store] using congrArg e.embed empty
      | some i =>
        have empty := StagingPrivate.loaded_outside [] (Nat.zero_le R) a ha
        simpa [active,imageTape,Tape.absolute,publicLoad,Pipeline.store] using congrArg e.embed empty
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
  · right
    push Not at bounded
    obtain ⟨v,hv,w,cut,j,esc⟩ := bounded
    have partialRun := ((TapeSequence.first_trace offer core q prep.1).trans
      (.single (TapeSequence.handoff offer core q hprep))).trans (TapeSequence.second_trace offer core q cut)
    have full := TapeSequence.first_trace mid clear (fun _ => .seekLeft) partialRun
    refine ⟨_,_,j,full,?_⟩
    change (w.tape j).pos < -(R:ℤ) ∨ (R:ℤ) < (w.tape j).pos
    omega

end StagingDigit

end NearSquareRoot
end Computability
end OAI
