import OAI.Computability.NearSquareRoot.ScheduleMultiplicationInputs
import OAI.Computability.NearSquareRoot.ScheduleMachineRun
import OAI.Computability.NearSquareRoot.ScheduleAsymptotic
import OAI.Computability.NearSquareRoot.InterchangeSplitCompose

/-!
# Reduction of uniform multiplication to a restartable physical executor

The physical input setup and the slot executor are each a single finite-control
machine. A slot receives the index and the clock exponent on the two counter
heads. Every failed slot restores its full tape layout. The hypotheses below
separate these implementation obligations from the time and space analysis of
the round controller.

The polynomial fallback is used to bound the space of one halting execution.
Determinism identifies its halting time with that witnessed by each of the
arbitrarily fast comparison candidates.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ScheduleMachine

open IntegerMultiplication Filter

variable {A G Q I σ α : Type}

/-- Components used for every bit length and requested exponent. -/
structure MultiplierDriver (A G Q I σ α : Type) where
  bit : Bool → A
  sep : A
  blank : A
  mark : A
  inp : I
  out : I
  setup : TM.Rule A G (Index I)
  beginSetup : G
  executor : TM.Rule A Q (Index I)
  beginTrial : Q
  accept : Q → Bool
  work : (n : ℕ) → Input n → I → TM.Tape A
  tick : σ → Schedule.Tick σ α
  candidate : (n : ℕ) → Input n → ℕ → σ

namespace MultiplierDriver

variable (d : MultiplierDriver A G Q I σ α)

noncomputable def initial (n : ℕ) (x : Input n) :=
  initialConfig d.beginSetup (.inr d.inp : Index I) d.bit d.sep d.blank (xbits x) (ybits x)

def output (n : ℕ) (x : Input n) (tape : Index I → TM.Tape A) : Prop :=
  ∃ z : List Bool, TM.whole d.blank (z.map d.bit) (tape (.inr d.out)) ∧
    z.length = 2*n ∧ bitValue z = bitValue (xbits x) * bitValue (ybits x)

def answer (n : ℕ) (x : Input n) (i b : ℕ) := Schedule.tryFor d.tick b (d.candidate n x i)

variable [Finite A]
noncomputable abbrev outer := rule d.blank d.mark d.beginTrial d.executor d.accept
noncomputable abbrev physical :=
  TapeSequence.rule d.setup d.outer (.inr d.beginTrial : PC Q)

private def radius (D E n s : ℕ) : ℕ := (D+E+4)*(n+s+2)

/-- The finite machines are independently charged at their actual tape transition
level. The only comparison bound here is on successful fixed-index attempts. -/
structure Implements (D E C K p : ℕ) : Prop where
  letters : Function.Injective d.bit ∧ (∀ b, d.bit b ≠ d.sep ∧ d.bit b ≠ d.blank) ∧
    d.sep ≠ d.blank ∧ d.blank ≠ d.mark
  origins : ∀ n x j, (d.work n x j).pos = 0
  prepare : ∀ n x, ∃ t z, t ≤ D*(n+1) ∧
    Trace (TM.advance d.setup) (d.initial n x) t z ∧ TM.advance d.setup z = none ∧
    z.tape = counters d.blank d.mark 0 0 (d.work n x)
  slots : ∀ n x i a, let r : ℤ := E*(n+i+a+1 : ℕ)
    AttemptReturns d.blank d.mark d.beginTrial d.executor d.accept (d.work n x)
      (fun _ => -r) (fun _ => r) (fun _ c => d.output n x c.tape) (d.answer n x)
      (fun j e => C*(2^e+j+e+1)) i a
  fallback : ∀ n x, ∃ t v, d.answer n x 0 t = some v ∧ t ≤ K*(n+1)^p
  fast : ∀ j : ℕ, ∃ (i : ℕ) (H : ℝ), 0 ≤ H ∧ ∀ᶠ n in atTop, ∀ x : Input n,
    ∃ t v, d.answer n x i t = some v ∧
      (t : ℝ) ≤ H*n*logScale n ^ ((1 : ℝ)/2 + 1/(j+2 : ℝ))

omit [Finite A] in
private theorem widen {R : Type} {M : TM.Rule A R (Index I)} {x z t} {B V : ℕ}
    (h : FencedRun M (fun _ => -(B : ℤ)) (fun _ => B) x t z) (hv : B ≤ V) :
    FencedRun M (fun _ => -(V : ℤ)) (fun _ => V) x t z := by
  refine ⟨h.1, fun u hu c hrun j => ?_⟩
  obtain ⟨left,right⟩ := h.2 u hu c hrun j
  dsimp only at left right ⊢
  omega

private def charges (C i a : ℕ) := C*(2^a+i+a+1)+(i+3)

private theorem charge_bound (C r : ℕ) :
    Schedule.slotCost (charges C) 0 r ≤ 4*((C+3)+1)*2^r := by
  have h (i a : ℕ) : charges C i a ≤ (C+3)*(2^a+i+a+1) := by
    unfold charges
    rw [Nat.add_mul]
    have hz : 0 < 2^a := by positivity
    omega
  exact (Nat.le_add_right _ _).trans (Schedule.round_charge_le h r)

private theorem successful_round {D E C K p n s : ℕ} (h : d.Implements D E C K p) (x : Input n)
    {v : α} (ho : Schedule.through (d.answer n x) s = some v) :
    ∃ t z, t ≤ D*(n+1)+1 + Schedule.prefixCost (fun r => Schedule.slotCost (charges C) 0 r) s ∧
      FencedRun d.physical (fun _ => -(radius D E n s : ℤ)) (fun _ => radius D E n s)
        (TapeSequence.relabel Sum.inl (d.initial n x)) t z ∧
      TM.advance d.physical z = none ∧ d.output n x z.tape := by
  let B := radius D E n s
  have hB : 2*s+3 ≤ B := by dsimp [B,radius]; nlinarith
  have fits (i a : ℕ) (hia : i+a ≤ s) (j : Index I) :
      -(B : ℤ) + (i+3 : ℕ) ≤ (counters d.blank d.mark i a (d.work n x) j).pos ∧
      (counters d.blank d.mark i a (d.work n x) j).pos ≤ (B : ℤ) - (i+3 : ℕ) := by
    cases j with
    | inr j =>
      change _ ≤ (d.work n x j).pos ∧ (d.work n x j).pos ≤ _
      rw [h.origins]; omega
    | inl j =>
      cases j
      · change _ ≤ (i : ℤ) ∧ (i : ℤ) ≤ _
        omega
      · change _ ≤ (a : ℤ) ∧ (a : ℤ) ≤ _
        omega
  have attempts (i a : ℕ) (hia : i+a < s) :
      AttemptReturns d.blank d.mark d.beginTrial d.executor d.accept (d.work n x)
        (fun _ => -(B : ℤ)) (fun _ => B) (fun _ c => d.output n x c.tape)
        (d.answer n x) (fun j e => C*(2^e+j+e+1)) i a := by
    obtain ⟨t,z,hc,run,hhalt,how⟩ := h.slots n x i a
    have hle : E*(n+i+a+1) ≤ B := by
      dsimp [B,radius]
      exact Nat.mul_le_mul (by omega) (by omega)
    exact ⟨t,z,hc,widen run hle,hhalt,how⟩
  obtain ⟨z,t,ht,body,hz,correct⟩ := through_run h.letters.2.2.2 s fits attempts ho
  obtain ⟨u,g,hu,pre,hg,htapes⟩ := h.prepare n x
  have hpre : FencedRun d.setup (fun _ => -(B : ℤ)) (fun _ => B) (d.initial n x) u g := by
    have hle : D*(n+1) ≤ B := by
      dsimp [B,radius]
      exact Nat.mul_le_mul (by omega) (by omega)
    apply fencedRun_of_call_clock pre (D*(n+1)) hu
    intro j
    have initialPos : ((d.initial n x).tape j).pos = 0 := by
      simp [initial,initialConfig,TM.Tape.loaded]
    rw [initialPos]
    omega
  have afterSetup : FencedRun d.outer (fun _ => -(B : ℤ)) (fun _ => B)
      ⟨.inr d.beginTrial,g.tape⟩ t z := by
    simpa [htapes,slot] using body
  have total := TapeSequence.run_fenced d.setup d.outer (.inr d.beginTrial) hpre hg afterSetup
  have halted := (TapeSequence.run d.setup d.outer (.inr d.beginTrial) pre hg afterSetup.1 hz).2
  change t ≤ Schedule.prefixCost (fun r => Schedule.slotCost (charges C) 0 r) s at ht
  exact ⟨u+1+t,_,by omega,total,halted,correct⟩



/-- Once the common executor and its fixed-index candidates satisfy their local
contracts, one compiled tape machine satisfies the independent specification.
Neither the machine nor the visited-space constant depends on the exponent. -/
theorem uniformMultiplicationSpec [Finite G] [Finite Q] [Fintype I]
    {D E C K p : ℕ} (h : d.Implements D E C K p) : UniformMultiplicationSpec := by
  classical
  let R := (D+E+4) * (Nat.clog 2 K+p+4)
  let S := Fintype.card (Index I) * (2*R+1)
  have halts (n : ℕ) (x : Input n) :
      ∃ t z, Trace (TM.advance d.physical) (TapeSequence.relabel Sum.inl (d.initial n x)) t z ∧
        TM.advance d.physical z = none ∧ d.output n x z.tape ∧
        VisitsAtMost d.physical (TapeSequence.relabel Sum.inl (d.initial n x)) t (S*n) := by
    obtain ⟨t,v,hrun,ht⟩ := h.fallback n x
    obtain ⟨s,hs,hok⟩ := Schedule.polynomial_fallback_round hrun ht
    obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp hok
    obtain ⟨u,z,_,run,halt,correct⟩ := successful_round d h x hv
    have hradius : radius D E n s ≤ R * n := scheduler_radius D E K p n s x.property hs
    have wide := widen run hradius
    exact ⟨u,z,run.1,halt,correct,visitsAtMost_of_linear_fence R n x.property wide.2⟩
  choose time finish actual stop output visited using halts
  let cost (_n : ℕ) (_x : Input _n) (s : ℕ) := Schedule.slotCost (charges C) 0 s
  have ht : AllEpsilonBounds (Schedule.worstTime time) := by
    apply Schedule.allEpsilonBounds_of_schedule d.tick d.candidate time cost
      (4*((C+3)+1)) (D+1) (fun _ _ s => charge_bound C s) _ h.fast
    intro n x s yes
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp yes
    obtain ⟨t,z,hbound,run,halt,_⟩ := successful_round d h x hv
    obtain ⟨heq,_⟩ := halting_trace_unique (actual n x) (stop n x) run.1 halt
    change time n x ≤ (D+1)*(n+1) + Schedule.prefixCost (fun r => Schedule.slotCost (charges C) 0 r) s
    rw [heq, Nat.add_mul]
    omega
  refine ⟨A,G ⊕ PC Q,Index I,inferInstance,inferInstance,inferInstance,d.bit,d.sep,d.blank,
    .inr d.inp,.inr d.out,.inl d.beginSetup,d.physical,Schedule.worstTime time,S,
    h.letters.1,h.letters.2.1,h.letters.2.2.1,(allEpsilonBounds_iff_forall_pos _).mp ht,?_⟩
  intro n hn b c hb hc
  obtain ⟨x,rfl,rfl⟩ := exists_input n hn b c hb hc
  obtain ⟨bits,word,length,value⟩ := output n x
  exact ⟨time n x,finish n x,bits,actual n x,stop n x,word,length,value,
    Schedule.le_worstTime time n x,visited n x⟩

end MultiplierDriver
end ScheduleMachine

end NearSquareRoot
end Computability
end OAI
