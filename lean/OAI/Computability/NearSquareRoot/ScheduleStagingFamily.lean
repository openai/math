import OAI.Computability.NearSquareRoot.ScheduleStagingProduct
import OAI.Computability.NearSquareRoot.ScheduleStagingFailureDigit
import OAI.Computability.NearSquareRoot.ScheduleStagingFailure
import OAI.Computability.NearSquareRoot.ScheduleChunkCompare

/-! # Finite, fenced physical candidates on a shared alphabet and tape bank -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingProduct

open IntegerMultiplication Code Bits TM CommonAlphabet CommonAlphabet.Pipeline
open ChunkControl (Driver)
open ChunkLoop ChunkTask ChunkPhases Filter

variable {I Q : Type} [Fintype I] [DecidableEq I]

noncomputable local instance (d : Driver) : DecidableEq (StagingControl.Letter d) := Classical.decEq _

noncomputable def guarded (d : Driver) (g : Rule Public.Letter Q (Index I)) (q : Q) :=
  StagingProtection.rule d (digit d g q) StagingDigit.start

omit [DecidableEq I] in
theorem call_or_overflow (d : Driver) (C : ℕ) (m : Operands → Word) (p : ChunkTask.Input)
    (g : Rule Public.Letter Q (Index I)) (q : Q) (T S : ℕ → ℕ)
    (callee : StagingCall.Computes g q m T S) (i : ℕ) (hi : i < p.count)
    (width : (digitReply m p i).length = 2*p.u) :
    StagingOuter.Call d C m p (digit d g q) StagingDigit.start (callBudget C p.n p.u (T p.u)) i ∨
      StagingFailure.BadCall d C m p (digit d g q) StagingDigit.start i := by
  let e := StagingLetters.encoding d
  let B := StagingControl.initialBottom d (input p)
  let R := StagingOuter.radius C p.n
  let query := digitQuery m p i
  let reg := StagingPhases.slot (p.bundle m i) (StagingPhases.request query)
  let shelves := (StagingControl.entry d B .digit reg).tape
  have widths := p.query_width m i
  let a : EqualWords := ⟨query,widths.1.trans widths.2.symm,widths.1.symm ▸ p.width_pos⟩
  have length : a.val.1.length = p.u := widths.1
  obtain ⟨n,hn,z,trace,halt,output,_⟩ := callee a
  rw [length] at hn
  have gR : 6*p.u+7 ≤ R := by
    have h := p.width_le
    dsimp [R,StagingOuter.radius]
    nlinarith
  rcases StagingDigit.run_or_overflow (StagingOpen.one d) e (StagingLetters.sentinel d)
    (StagingLetters.reserved d) g q shelves query.1 query.2 (digitReply m p i)
    widths.1 widths.2 trace halt output (StagingLetters.query d B (StagingControl.one_bottom ..) m p i)
      gR (StagingOuter.request_heads d C m p i hi) with good | fail
  · left
    obtain ⟨t,ht,run,stop⟩ := good
    have out := StagingLetters.reply d B (StagingControl.one_bottom ..) m p i (digitReply m p i) width
    change _ = Function.update shelves _ _ at out
    rw [← out] at run stop
    exact ⟨_,t,ht.trans (by unfold callBudget; dsimp [R]; omega),run,stop⟩
  · exact Or.inr fail

def HasWidth (m : Operands → Word) := ∀ a : EqualWords, (m a.val).length = 2*a.val.1.length
def Multiplies (m : Operands → Word) := ∀ a : EqualWords, bitValue (m a.val) = bitValue a.val.1 * bitValue a.val.2

private theorem reply_width {m : Operands → Word} (h : HasWidth m) (p : ChunkTask.Input) (i : ℕ) :
    (digitReply m p i).length = 2*p.u := by
  have size := p.query_width m i
  let a : EqualWords := ⟨_,size.1.trans size.2.symm,size.1.symm ▸ p.width_pos⟩
  simpa only [digitReply,digitQuery,a,size.1] using h a

/-- Every accepted execution on a valid split publishes the complete product.
There is no upper bound hypothesis on the resources used by the candidate. -/
theorem sound (d : Driver) (C : ℕ) (m : Operands → Word) (p : ChunkTask.Input)
    (g : Rule Public.Letter Q (Index I)) (q : Q) (T S : ℕ → ℕ)
    (ctl : StagingPhases.Calls d.load d.test d.prepare d.collect d.emit C m p ((answer m p).map Ltr.bit))
    (callee : StagingCall.Computes g q m T S) (width : HasWidth m) (correct : Multiplies m)
    {t y} (run : Trace (advance (guarded d g q)) (StagingProtection.initial d C p.n (input p)) t y)
    (halt : advance (guarded d g q) y = none) (ok : y.pc.1 = false) :
    whole (StagingProtection.blank d) ((answer m p).map (StagingProtection.bit d)) (y.tape none) ∧
    (answer m p).length = 2*p.n ∧ bitValue (answer m p) = bitValue p.x * bitValue p.y := by
  have hz := answer_spec m correct p
  refine ⟨StagingFailure.protected_output d C m p (digit d g q) StagingDigit.start (T:=callBudget C p.n p.u (T p.u)) hz.1 ctl
    (fun i _ => reply_width width p i) ?_ run halt ok,hz⟩
  exact fun i hi => call_or_overflow d C m p g q T S callee i hi (reply_width width p i)

/-- A successful complete execution of the guarded, clean-output multiplier. -/
noncomputable def Returns (d : Driver) (C : ℕ) (m : Operands → Word)
    (g : Rule Public.Letter Q (Index I)) (q : Q) (p : ChunkTask.Input) (t : ℕ) : Prop :=
  ∃ y, Trace (advance (guarded d g q)) (StagingProtection.initial d C p.n (input p)) t y ∧
    advance (guarded d g q) y = none ∧ y.pc.1 = false ∧
    whole (StagingProtection.blank d) ((answer m p).map (StagingProtection.bit d)) (y.tape none)

theorem returns (d : Driver) (C : ℕ) (m : Operands → Word) (p : ChunkTask.Input)
    (g : Rule Public.Letter Q (Index I)) (q : Q) (T S : ℕ → ℕ)
    (ctl : StagingPhases.Calls d.load d.test d.prepare d.collect d.emit C m p ((answer m p).map Ltr.bit))
    (callee : StagingCall.Computes g q m T S) (width : HasWidth m) (correct : Multiplies m)
    (fit : S p.u ≤ p.n) :
    ∃ t ≤ (26*C+1050)*((p.count+1)*(p.n+T p.u+1)), Returns d C m g q p t := by
  have hz := answer_spec m correct p
  obtain ⟨t,ht,done⟩ := StagingProtection.run d C m p (answer m p) hz.1 (digit d g q)
    StagingDigit.start ctl (fun i _ => reply_width width p i)
    (fun i hi => call d C m p g q T S callee i hi (reply_width width p i) fit)
  exact ⟨t,ht.trans (budget C p _),done⟩

/-- Any fixed genuinely linear-space digit machine with exponent e succeeds
on one fixed dyadic split. The bound includes every copy, sweep and publication. -/
theorem selected (d : Driver) (C : ℕ) (m : Operands → Word)
    (g : Rule Public.Letter Q (Index I)) (q : Q) (T S : ℕ → ℕ)
    (ctl : ∀ p : ChunkTask.Input, StagingPhases.Calls d.load d.test d.prepare d.collect d.emit C m p
      ((answer m p).map Ltr.bit))
    (callee : StagingCall.Computes g q m T S) (width : HasWidth m) (correct : Multiplies m)
    (L : ℕ) (linear : ∀ᶠ u : ℕ in atTop, S u ≤ L*(u+1))
    (e A : ℝ) (he : 0 ≤ e) (hA : 0 ≤ A)
    (time : ∀ᶠ u : ℕ in atTop, (T u : ℝ) ≤ A*u*logScale u^e) :
    ∃ k : ℕ, ∃ H : ℝ, 0 ≤ H ∧ ∀ᶠ n : ℕ in atTop, 2^k ≤ n ∧
      ∀ p : ChunkTask.Input, p.n = n → p.k = k →
        ∃ t, ((t+1 : ℕ):ℝ) ≤ H*n*logScale n^e ∧ Returns d C m g q p t := by
  obtain ⟨k,fit⟩ := Uniform.exists_dyadic_split L
  let D := 26*C+1050
  obtain ⟨H,hH,deadline⟩ := ChunkControl.fixed_deadline D k T e A he hA time
  obtain ⟨U,hU⟩ := eventually_atTop.mp linear
  refine ⟨k,H,hH,?_⟩
  filter_upwards [deadline,eventually_ge_atTop (2*2^k),eventually_ge_atTop (2^k*U)] with n ht hn hu
  obtain ⟨hr,hs⟩ := fit n hn
  refine ⟨hr,?_⟩
  intro p np kp
  have hr' : p.r = 2^k := by simp [ChunkTask.Input.r,kp]
  have small : U ≤ p.u := Uniform.cutoff_le_chunkWidth p.positive (by simpa [hr',np] using hu)
  have fitted : S p.u ≤ p.n := (hU p.u small).trans (by simpa [ChunkTask.Input.u,hr',np] using hs)
  obtain ⟨t,h,done⟩ := returns d C m p g q T S (ctl p) callee width correct fitted
  refine ⟨t,?_ ,done⟩
  apply le_trans _ (ht p np kp)
  exact_mod_cast Nat.add_le_add_right (h.trans (Nat.mul_le_mul_right _ (show D ≤ 6*D+16 by omega))) 1

end StagingProduct

end NearSquareRoot
end Computability
end OAI
