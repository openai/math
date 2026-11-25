import OAI.Computability.NearSquareRoot.ScheduleSchoolbook
import OAI.Computability.NearSquareRoot.ScheduleInterpreterTrial
import OAI.Computability.NearSquareRoot.ScheduleInterpreterSpace
import OAI.Computability.NearSquareRoot.ScheduleMultiplicationInputs

/-!
# Index-zero schoolbook trial

The fallback arm takes one actual multitape transition per tick and returns
its halted configuration on the next tick. The other arm runs the supplied
positive trials unchanged. Both are evaluated by the same bounded scheduler.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChunkFallback

open IntegerMultiplication
open Schedule (Tick tryFor)
open ScheduleMachine (Input xbits ybits)

structure Physical where
  A : Type
  Q : Type
  I : Type
  finiteA : Finite A
  finiteQ : Finite Q
  finiteI : Finite I
  bit : Bool → A
  sep : A
  blank : A
  inp : I
  out : I
  beginState : Q
  machine : TM.Rule A Q I
  time : ℕ
  space : ℕ
  bits : Function.Injective bit ∧ (∀ b, bit b ≠ sep ∧ bit b ≠ blank) ∧ sep ≠ blank ∧ inp ≠ out
  runs : ∀ n (u : Input n), ∃ t finish z,
    Trace (TM.advance machine) (initialConfig beginState inp bit sep blank (xbits u) (ybits u)) t finish ∧
    TM.advance machine finish = none ∧ TM.whole blank (z.map bit) (finish.tape out) ∧
    z.length = 2*n ∧ bitValue z = bitValue (xbits u) * bitValue (ybits u) ∧ t ≤ time*n^2 ∧
    VisitsAtMost machine (initialConfig beginState inp bit sep blank (xbits u) (ybits u)) t (space*n)

/-- One fixed witness serves every input length and every positive family. -/
noncomputable def schoolbook : Physical := Classical.choice (show Nonempty Physical by
  obtain ⟨A,Q,I,fa,fq,fi,bit,sep,blank,inp,out,q,m,C,S,inj,marked,ne,io,h⟩ := Schoolbook.schoolbook_machine
  exact ⟨⟨A,Q,I,fa,fq,fi,bit,sep,blank,inp,out,q,m,C,S,⟨inj,marked,ne,io⟩,
    fun n u => h n u.property _ _ (ScheduleMachine.xbits_length u) (ScheduleMachine.ybits_length u)⟩⟩)

abbrev Configuration := TM.Config schoolbook.A schoolbook.Q schoolbook.I

noncomputable def source (n : ℕ) (u : Input n) : Configuration :=
  initialConfig schoolbook.beginState schoolbook.inp schoolbook.bit schoolbook.sep schoolbook.blank
    (xbits u) (ybits u)

noncomputable abbrev slow : Configuration → Tick Configuration Configuration :=
  Uniform.tapeTick schoolbook.machine fun _ => true

def Output (n : ℕ) (u : Input n) (v : Configuration) : Prop :=
  ∃ z : List Bool, TM.whole schoolbook.blank (z.map schoolbook.bit) (v.tape schoolbook.out) ∧
    z.length = 2*n ∧ bitValue z = bitValue (xbits u) * bitValue (ybits u)

/-- Witnesses for the halt time and the output come from the compiled
schoolbook machine; determinism makes them apply to every accepted budget. -/
theorem slow_sound (n : ℕ) (u : Input n) {b v} (h : tryFor slow b (source n u) = some v) :
    Output n u v := by
  obtain ⟨t, _, run, halt, _⟩ := (Uniform.tapeTrial_iff _ _ _ _ _).1 h
  obtain ⟨s, y, z, hr, hs, out, len, val, _, _⟩ := schoolbook.runs n u
  obtain ⟨_, rfl⟩ := halting_trace_unique run halt hr hs
  exact ⟨z, out, len, val⟩

theorem slow_deadline (n : ℕ) (u : Input n) :
    ∃ t v, tryFor slow t (source n u) = some v ∧ t ≤ (schoolbook.time+1)*(n+1)^2 := by
  obtain ⟨t,v,_,run,halt,_,_,_,cost,_⟩ := schoolbook.runs n u
  refine ⟨t+1,v,(Uniform.tapeTrial_iff _ _ _ _ _).2 ⟨t,Nat.lt_succ_self _,run,halt,rfl⟩,?_⟩
  nlinarith

/-- Schoolbook also retains its physical linear bound for any cutoff, even
when the allotted budget exceeds its actual halting time. -/
theorem slow_space (n : ℕ) (u : Input n) (budget : ℕ) :
    VisitsAtMost schoolbook.machine (source n u) budget (schoolbook.space*n) := by
  obtain ⟨t,finish,z,run,halt,_,_,_,_,cells,hc,cover⟩ := schoolbook.runs n u
  exact ⟨cells,hc,fun b _ y sub i => cover b (Uniform.before_halt run halt sub) y sub i⟩

variable {σ α : Type}

/-- Inject an entire tick into one side of a sum of trial families. -/
private def mapTick {S V S' V' : Type} (st : S → S') (ans : V → V') : Tick S V → Tick S' V'
  | .abort => .abort
  | .done v => .done (ans v)
  | .more x => .more (st x)

noncomputable def tick (next : σ → Tick σ α) :
    Configuration ⊕ σ → Tick (Configuration ⊕ σ) (Configuration ⊕ α)
  | .inl x => mapTick Sum.inl Sum.inl (slow x)
  | .inr x => mapTick Sum.inr Sum.inr (next x)

noncomputable def start (positive : (n : ℕ) → Input n → ℕ → σ)
    (n : ℕ) (u : Input n) : ℕ → Configuration ⊕ σ
  | 0 => .inl (source n u)
  | i+1 => .inr (positive n u i)

def Correct (positive : (n : ℕ) → Input n → α → Prop) (n : ℕ) (u : Input n) :
    Configuration ⊕ α → Prop := Sum.elim (Output n u) (positive n u)

private theorem tryFor_left (next : σ → Tick σ α) (b : ℕ) (x : Configuration) :
    tryFor (tick next) b (.inl x) = (tryFor slow b x).map Sum.inl := by
  induction b generalizing x with
  | zero => rfl
  | succ b ih =>
    cases h : slow x with
    | more y => simpa only [tryFor,tick,h,mapTick] using ih y
    | done v => simp [tryFor,tick,h,mapTick]
    | abort => simp [tryFor,tick,h,mapTick]

/-- Positive trials retain exactly their original fuel semantics, including
abort and exhaustion. The global index is the local index plus one. -/
theorem tryFor_positive (next : σ → Tick σ α) (positive : (n : ℕ) → Input n → ℕ → σ)
    (n : ℕ) (u : Input n) (i b : ℕ) :
    tryFor (tick next) b (start positive n u (i+1)) =
      (tryFor next b (positive n u i)).map Sum.inr := by
  change tryFor (tick next) b (.inr (positive n u i)) = _
  generalize positive n u i = x
  induction b generalizing x with
  | zero => rfl
  | succ b ih =>
    cases h : next x with
    | more y => simpa only [tryFor,tick,h,mapTick] using ih y
    | done v => simp [tryFor,tick,h,mapTick]
    | abort => simp [tryFor,tick,h,mapTick]

/-- Any sound family on the positive indices extends to a single sound tick
with an unconditional quadratic deadline at index zero. No fallback behavior
is assumed of the supplied candidates, including at short input lengths. -/
theorem with_schoolbook (next : σ → Tick σ α) (positive : (n : ℕ) → Input n → ℕ → σ)
    (correct : (n : ℕ) → Input n → α → Prop)
    (sound : ∀ n u i b v, tryFor next b (positive n u i) = some v → correct n u v) :
    (∀ n u i b v, tryFor (tick next) b (start positive n u i) = some v → Correct correct n u v) ∧
    (∃ K : ℕ, ∀ n u, ∃ t v, tryFor (tick next) t (start positive n u 0) = some v ∧
      t ≤ K*(n+1)^2) ∧
    (∀ n u i b, tryFor (tick next) b (start positive n u (i+1)) =
      (tryFor next b (positive n u i)).map Sum.inr) := by
  refine ⟨?_, ⟨schoolbook.time+1, ?_⟩, tryFor_positive next positive⟩
  · intro n u i b v run
    cases i with
    | zero =>
      change tryFor (tick next) b (.inl (source n u)) = some v at run
      rw [tryFor_left] at run
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp run
      exact slow_sound n u hz
    | succ i =>
      rw [tryFor_positive] at run
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp run
      exact sound n u i b z hz
  · intro n u
    obtain ⟨t,v,ht,hb⟩ := slow_deadline n u
    refine ⟨t, .inl v, ?_, hb⟩
    change tryFor (tick next) t (.inl (source n u)) = _
    rw [tryFor_left,ht]
    rfl

end ChunkFallback

end NearSquareRoot
end Computability
end OAI
