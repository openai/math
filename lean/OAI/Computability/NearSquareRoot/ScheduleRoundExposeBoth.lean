import OAI.Computability.NearSquareRoot.ScheduleRoundExpose
import OAI.Computability.NearSquareRoot.InterchangeSplitCompose

/-! # Exposing both the candidate index and budget exponent in one physical call -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RoundExpose
open IntegerMultiplication TM

section
variable {A Q I : Type}

/-- Freeze the other bank while running the current machine. -/
private def bankRule (b : Bool) (m : Rule A Q I) : Rule A Q (Bool × I) := fun q v =>
  (m q (fun i => v (b,i))).map fun (q',acts) => (q',fun j =>
    if j.1 = b then acts j.2 else (v j,.stay))

private def bankConfig (b : Bool) (x : Config A Q I) (w : I → Tape A) : Config A Q (Bool × I) :=
  ⟨x.pc, fun j => if j.1 = b then x.tape j.2 else w j.2⟩

private theorem bank_advance (b : Bool) (m : Rule A Q I) (x : Config A Q I) (w : I → Tape A) :
    advance (bankRule b m) (bankConfig b x w) = (advance m x).map fun y => bankConfig b y w := by
  simp only [advance,bankRule,bankConfig,ite_true]
  cases op : m x.pc (fun i => (x.tape i).view 0) with
  | none => rfl
  | some a =>
    simp only [Option.map_some,Option.some.injEq,Config.mk.injEq,true_and]
    funext j
    by_cases hj : j.1 = b
    · simp [hj]
    · simp [hj]
      exact SM.Action.apply_stay _

private theorem bank_trace (b : Bool) (m : Rule A Q I) (w : I → Tape A) {x y t}
    (h : Trace (advance m) x t y) :
    Trace (advance (bankRule b m)) (bankConfig b x w) t (bankConfig b y w) := by
  induction h with
  | nil => exact .nil _
  | cons step _ ih => exact .cons (by rw [bank_advance,step]; rfl) ih

private theorem bank_fenced (b : Bool) (m : Rule A Q I) (w : I → Tape A) {x y t} (l h : ℤ)
    (hw : ∀ j, l ≤ (w j).pos ∧ (w j).pos ≤ h)
    (r : FencedRun m (fun _ => l) (fun _ => h) x t y) :
    FencedRun (bankRule b m) (fun _ => l) (fun _ => h) (bankConfig b x w) t (bankConfig b y w) := by
  refine ⟨bank_trace b m w r.1, ?_⟩
  intro u hu c hc j
  obtain ⟨z,hz,_⟩ := trace_split r.1 hu
  rw [trace_endpoint_unique hc (bank_trace b m w hz)]
  by_cases hj : j.1 = b
  · simpa [bankConfig,hj] using r.2 u hu z hz j.2
  · simpa [bankConfig,hj] using hw j.2

end

/-- Four tapes, organised in two banks of one persistent cursor and one unary output. -/
def bothRule := TapeSequence.rule (bankRule false rule) (bankRule true rule) .scan

private def tapes (i a : ℕ) (filled : Bool) (j : Bool × Bool) : Tape (Option Bool) :=
  let k := if j.1 then a else i
  if j.2 then word (if filled then k else 0) 0 else cursor k

def bothStart (i a : ℕ) : Config (Option Bool) (State ⊕ State) (Bool × Bool) :=
  ⟨.inl .scan,tapes i a false⟩

def bothDone (i a : ℕ) : Config (Option Bool) (State ⊕ State) (Bool × Bool) :=
  ⟨.inr .done,tapes i a true⟩

private theorem widen {s s' : ℕ} {x y t} (hle : s ≤ s')
    (h : FencedRun rule (fun _ => -1) (fun _ => (s:ℤ)) x t y) :
    FencedRun rule (fun _ => -1) (fun _ => (s':ℤ)) x t y :=
  ⟨h.1, fun u hu c r j => ⟨(h.2 u hu c r j).1, (h.2 u hu c r j).2.trans (by change (s:ℤ) ≤ s'; exact_mod_cast hle)⟩⟩

/-- The four-tape call restores both persistent heads and prepares both unary words.
Its time includes the transition between banks. Its fences are common to all phases. -/
theorem expose_both (i a : ℕ) :
    FencedRun bothRule (fun _ => -1) (fun _ => (max i a : ℕ)) (bothStart i a)
      (2*(i+a)+5) (bothDone i a) := by
  let x := cfg .scan i 0 0
  let x' := cfg .done i 0 i
  let y := cfg .scan a 0 0
  have first := bank_fenced false rule y.tape (-1) (max i a : ℕ) (by
    intro j; cases j <;> simp [y,cfg,cursor,RoundControl.cursor,word]) (widen (le_max_left i a) (expose i))
  have second := bank_fenced true rule x'.tape (-1) (max i a : ℕ) (by
    intro j; cases j <;> simp [x',cfg,cursor,RoundControl.cursor,word]) (widen (le_max_right i a) (expose a))
  have middle : bankConfig true y x'.tape =
      (⟨.scan, (bankConfig false x' y.tape).tape⟩ : Config _ _ _) := by
    unfold bankConfig
    congr 1
    funext j
    obtain ⟨b,k⟩ := j
    cases b <;> rfl
  rw [middle] at second
  have halt : advance (bankRule false rule) (bankConfig false x' y.tape) = none := by
    rw [bank_advance]
    rfl
  have h := TapeSequence.run_fenced (bankRule false rule) (bankRule true rule) .scan first halt second
  have init : bothStart i a = TapeSequence.relabel Sum.inl (bankConfig false x y.tape) := by
    apply congrArg (Config.mk _)
    funext j
    rcases j with ⟨b,k⟩
    cases b <;> cases k <;> rfl
  have fin : bothDone i a = TapeSequence.relabel Sum.inr (bankConfig true (cfg .done a 0 a) x'.tape) := by
    apply congrArg (Config.mk _)
    funext j
    rcases j with ⟨b,k⟩
    cases b <;> cases k <;> rfl
  rw [init,fin,show 2*(i+a)+5 = 2*i+2+1+(2*a+2) by omega]
  exact h

theorem expose_both_visits (i a : ℕ) :
    VisitsAtMost bothRule (bothStart i a) (2*(i+a)+5) (4*(max i a + 2)) := by
  convert visitsAtMost_of_common_fence _ _ (expose_both i a).2 using 1
  simp
  omega

theorem both_halt (i a : ℕ) : advance bothRule (bothDone i a) = none := rfl

theorem both_persistent (i a : ℕ) (b : Bool) :
    (bothDone i a).tape (b,false) = (bothStart i a).tape (b,false) := rfl

theorem both_unary (i a : ℕ) (b : Bool) :
    (bothDone i a).tape (b,true) = Tape.loaded none ((List.replicate (if b then a else i) true).map some) :=
  word_at_zero _

end RoundExpose

end NearSquareRoot
end Computability
end OAI
