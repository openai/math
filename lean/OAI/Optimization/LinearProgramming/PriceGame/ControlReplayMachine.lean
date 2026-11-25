import OAI.Optimization.LinearProgramming.PriceGame.ControlPhaseMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignGuarded

/-! A physical reply-replay engine. The only retained control values are the public
unary dimension, the remaining Boolean word, and the finite campaign stack. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native
namespace Replay

open ExactQuantumFactoring.BitStackProgram Procedure
open Wire

abbrev Context := ℕ × List Bool
abbrev Running := ℕ × (List Bool × Driver.PC)
abbrev State := Running ⊕ (Bool ⊕ PackedQuery)

def contextCode : Context → List Bool := prodCode unaryCode id
def runningCode : Running → List Bool := prodCode unaryCode (prodCode id combinedCode)
def stoppedCode : Bool ⊕ PackedQuery → List Bool := sumCode boolCode packedQueryCode
def stateCode : State → List Bool := sumCode runningCode stoppedCode

def live (n : ℕ) (bs : List Bool) (s : Driver.PC) : State := .inl (n,bs,s)
def done (b : Bool) : State := .inr (.inl b)
def pending (q : PackedQuery) : State := .inr (.inr q)

/-- Execute one internal instruction or consume one previously recorded answer. -/
def respond (z : Context) : Driver.Action → State
  | .proceed s => live z.1 z.2 s
  | .halt b => done b
  | .ask q f t => match z.2 with
    | [] => pending q
    | b::bs => live z.1 bs (if b then t else f)

def advance (micro : ℕ × Driver.PC → Driver.Action) : State → State
  | .inl (n,bs,s) => respond (n,bs) (micro (n,s))
  | .inr stopped => .inr stopped

private noncomputable def liveP : Procedure runningCode stateCode (Sum.inl : Running → State) :=
  (prepend runningCode [false]).result (by intro _; rfl)
private noncomputable def doneP : Procedure boolCode stateCode done :=
  (prepend boolCode [true,false]).result (by intro _; rfl)
private noncomputable def pendingP : Procedure packedQueryCode stateCode pending :=
  (prepend packedQueryCode [true,true]).result (by intro _; rfl)

private def actionView : Driver.Action → (Driver.PC ⊕ (Join.OuterReply ⊕ Bool))
  | .proceed s => .inl s
  | .ask q f t => .inr (.inl (q,f,t))
  | .halt b => .inr (.inr b)

private def defaultPC : Driver.PC := .campaign default

noncomputable def respondP : Procedure (prodCode contextCode Join.actionCode) stateCode
    (fun z => respond z.1 z.2) := by
  let c := first contextCode combinedCode
  let n := (first unaryCode id).comp c
  let bs := (second unaryCode id).comp c
  let keep := liveP.comp (n.pair (bs.pair (second contextCode combinedCode)))

  let ctx := first contextCode Join.outerReplyCode
  let pad := (first unaryCode id).comp ctx
  let tape := (second unaryCode id).comp ctx
  let r := second contextCode Join.outerReplyCode
  let q := (first packedQueryCode (prodCode combinedCode combinedCode)).comp r
  let ft := (second packedQueryCode (prodCode combinedCode combinedCode)).comp r
  let next := conditional (head.comp tape) ((second combinedCode combinedCode).comp ft)
    ((first combinedCode combinedCode).comp ft)
  let more := liveP.comp (pad.pair ((tail.comp tape).pair next))
  let ask := conditional (isEmpty.comp tape) (pendingP.comp q) more
  let halt := doneP.comp (second contextCode boolCode)
  let dispatch := Join.contextCases (default,defaultPC,defaultPC) false ask halt
  let go := Join.contextCases defaultPC (Sum.inr false) keep dispatch
  let raw := go.precompose (fun z : Context × Driver.Action => (z.1,actionView z.2))
  apply (raw.congrEncoding (ec := prodCode contextCode Join.actionCode) (ed := stateCode)
    (by rintro ⟨c,a⟩; cases a <;> rfl) (by intro _; rfl)).congrFun
  rintro ⟨⟨n,bs⟩,a⟩
  cases a with
  | proceed => rfl
  | halt => rfl
  | ask q f t => cases bs with | nil => rfl | cons b bs => cases b <;> rfl

noncomputable def advanceP {micro : ℕ × Driver.PC → Driver.Action}
    (stepP : Procedure (prodCode unaryCode combinedCode) Join.actionCode micro) :
    Procedure stateCode stateCode (advance micro) := by
  let pad := first unaryCode (prodCode id combinedCode)
  let rest := second unaryCode (prodCode id combinedCode)
  let bs := (first id combinedCode).comp rest
  let s := (second id combinedCode).comp rest
  let next := respondP.comp ((pad.pair bs).pair (stepP.comp (pad.pair s)))
  let same : Procedure stoppedCode stateCode (Sum.inr : Bool ⊕ PackedQuery → State) :=
    (prepend stoppedCode [true]).result (by intro _; rfl)
  exact (casesSum next same).congrFun (by rintro (r|t) <;> rfl)

theorem stopped_fixed (micro : ℕ × Driver.PC → Driver.Action) (k : ℕ) (a : Bool ⊕ PackedQuery) :
    (advance micro)^[k] (Sum.inr a) = .inr a := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

theorem complete {P : Driver.PC → Prop} {o e tr ticks} (actual : Driver.GuardedSteps P o tr ticks e)
    {micro : ℕ × Driver.PC → Driver.Action} (n : ℕ)
    (correct : ∀ s, P s → micro (n,s) = Driver.step s) {b : Bool}
    (endStep : micro (n,e) = .halt b) (tail : List Bool) :
    (advance micro)^[ticks+1] (live n (tr.map Prod.snd ++ tail) o) = done b := by
  induction actual with
  | refl s =>
    change respond (n,tail) (micro (n,s)) = done b
    rw [endStep]
    rfl
  | silent hs h _ ih =>
    rw [Function.iterate_succ_apply]
    simp only [live,advance,correct _ hs,h,respond]
    exact ih endStep
  | answer bit hs h _ ih =>
    rw [Function.iterate_succ_apply]
    simp only [List.map_cons,List.cons_append,live,advance,correct _ hs,h,respond]
    exact ih endStep

theorem short {P : Driver.PC → Prop} {o e tr ticks} (actual : Driver.GuardedSteps P o tr ticks e)
    {micro : ℕ × Driver.PC → Driver.Action} (n : ℕ)
    (correct : ∀ s, P s → micro (n,s) = Driver.step s) (k : ℕ) (hk : k < tr.length) :
    (advance micro)^[ticks+1] (live n ((tr.take k).map Prod.snd) o) = pending tr[k].1 := by
  induction actual generalizing k with
  | refl => simp at hk
  | silent hs h _ ih =>
    rw [Function.iterate_succ_apply]
    simp only [live,advance,correct _ hs,h,respond]
    exact ih k hk
  | answer bit hs h _ ih =>
    rw [Function.iterate_succ_apply]
    cases k with
    | zero =>
      simp only [List.take_zero,List.map_nil,live,advance,correct _ hs,h,respond,List.getElem_cons_zero]
      exact stopped_fixed _ _ _
    | succ k =>
      simp only [List.take_succ_cons,List.map_cons,live,advance,correct _ hs,h,respond,
        List.getElem_cons_succ]
      exact ih k (by simpa using hk)

/-- Extra iterations are harmless after the final sign or first unserved request. -/
theorem more {micro : ℕ × Driver.PC → Driver.Action} {m k : ℕ} {s : State} {out : Bool ⊕ PackedQuery}
    (found : (advance micro)^[m] s = .inr out) (hk : m ≤ k) : (advance micro)^[k] s = .inr out := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm,Function.iterate_add_apply,found,stopped_fixed]

end Replay
end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
