import OAI.Computability.NearSquareRoot.ScheduleStagingRaw
import OAI.Computability.NearSquareRoot.ScheduleStagingDigit
import OAI.Computability.NearSquareRoot.ScheduleStagingLetters
import OAI.Computability.NearSquareRoot.ScheduleStagingOuterOutput

/-!
# Chunked multiplication over one fixed tape alphabet

The caller's finite tape alphabet is determined by its five fixed commands.
Any digit machine over the four public letters runs in the private bank,
independently of its finite control and of its original source alphabet.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingProduct

open IntegerMultiplication Code Bits TM CommonAlphabet CommonAlphabet.Pipeline
open ChunkControl (Driver)
open ChunkLoop ChunkTask ChunkPhases

variable {I Q : Type} [Fintype I] [DecidableEq I]

noncomputable local instance (d : Driver) : DecidableEq (StagingControl.Letter d) := Classical.decEq _

noncomputable def digit (d : Driver) (g : Rule Public.Letter Q (Index I)) (q : Q) :=
  StagingDigit.rule (StagingOpen.one d) (StagingLetters.encoding d) (StagingLetters.sentinel d)
    (StagingLetters.reserved d) g q

noncomputable def machine (d : Driver) (g : Rule Public.Letter Q (Index I)) (q : Q) :=
  StagingOuterOutput.rule d (digit d g q) StagingDigit.start

def callBudget (C n u ticks : ℕ) := 4*u+ticks+5*StagingOuter.radius C n+11

def radius (C n : ℕ) := StagingOuter.radius C n+2*n+1

omit [DecidableEq I] in
theorem call (d : Driver) (C : ℕ) (m : Operands → Word) (p : ChunkTask.Input)
    (g : Rule Public.Letter Q (Index I)) (q : Q) (T S : ℕ → ℕ)
    (callee : StagingCall.Computes g q m T S) (i : ℕ) (hi : i < p.count)
    (width : (digitReply m p i).length = 2*p.u) (fit : S p.u ≤ p.n) :
    StagingOuter.Call d C m p (digit d g q) StagingDigit.start (callBudget C p.n p.u (T p.u)) i := by
  let e := StagingLetters.encoding d
  let B := StagingControl.initialBottom d (input p)
  let R := StagingOuter.radius C p.n
  let query := digitQuery m p i
  let reg := StagingPhases.slot (p.bundle m i) (StagingPhases.request query)
  let shelves := (StagingControl.entry d B .digit reg).tape
  have widths := p.query_width m i
  let a : EqualWords := ⟨query,widths.1.trans widths.2.symm,widths.1.symm ▸ p.width_pos⟩
  have length : a.val.1.length = p.u := widths.1
  obtain ⟨n,hn,z,trace,halt,output,visits⟩ := callee a
  rw [length] at hn visits
  have gR : 6*p.u+7 ≤ R := by
    have h := p.width_le
    dsimp [R,StagingOuter.radius]
    nlinarith
  have sR : S p.u+2*p.u ≤ R := by
    have h := p.width_le
    dsimp [R,StagingOuter.radius]
    nlinarith
  obtain ⟨t,ht,run,stop⟩ := StagingDigit.run (StagingOpen.one d) e (StagingLetters.sentinel d)
    (StagingLetters.reserved d) g q shelves query.1 query.2 (digitReply m p i)
    widths.1 widths.2 trace halt output visits (StagingLetters.query d B (StagingControl.one_bottom ..) m p i)
      gR sR (StagingOuter.request_heads d C m p i hi)
  have out := StagingLetters.reply d B (StagingControl.one_bottom ..) m p i (digitReply m p i) width
  change _ = Function.update shelves _ _ at out
  rw [← out] at run stop
  exact ⟨_,t,ht.trans (by unfold callBudget; dsimp [R]; omega),run,stop⟩

theorem budget (C : ℕ) (p : ChunkTask.Input) (t : ℕ) :
    (p.count+1)*(6*(C*(p.n+1))+callBudget C p.n p.u t+8)+1+2*p.n ≤
      (26*C+1050)*((p.count+1)*(p.n+t+1)) := by
  let w := p.n+t+1
  have u := p.width_le
  have h : 6*(C*(p.n+1))+callBudget C p.n p.u t+8 ≤ (26*C+1047)*w := by
    unfold callBudget StagingOuter.radius w
    rw [Nat.add_mul]
    have le := Nat.mul_le_mul_left (26*C) (show p.n+1 ≤ p.n+t+1 by omega)
    nlinarith
  have mul := Nat.mul_le_mul_left (p.count+1) h
  rw [show (p.count+1)*((26*C+1047)*w) = (26*C+1047)*((p.count+1)*w) by ring] at mul
  have big : w ≤ (p.count+1)*w := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  change _ ≤ (26*C+1050)*((p.count+1)*w)
  rw [show (26*C+1050)*((p.count+1)*w) = (26*C+1047)*((p.count+1)*w)+3*((p.count+1)*w) by ring]
  dsimp only [w] at big mul ⊢
  omega

/-- The output consists of bare MSF bits on an initially blank tape.
Every successful prefix stays within the same absolute radius, independent
of the parameters and of the candidate digit program. -/
noncomputable def Completed (d : Driver) (C : ℕ) (g : Rule Public.Letter Q (Index I)) (q : Q)
    (m : Operands → Word) (T : ℕ → ℕ) (p : ChunkTask.Input) : Prop :=
  let R := radius C p.n
  ∃ t ≤ (26*C+1050)*((p.count+1)*(p.n+T p.u+1)), ∃ z,
    FencedRun (machine d g q) (fun _ => -(R:ℤ)) (fun _ => (R:ℤ))
      (StagingOuterOutput.initial d C p) t z ∧ advance (machine d g q) z = none ∧
    whole (StagingOuterOutput.blank d) ((answer m p).map (StagingOuterOutput.bit d)) (z.tape none) ∧
    (answer m p).length = 2*p.n ∧ bitValue (answer m p) = bitValue p.x * bitValue p.y

theorem complete (d : Driver) (C : ℕ) (m : Operands → Word) (p : ChunkTask.Input)
    (g : Rule Public.Letter Q (Index I)) (q : Q) (T S : ℕ → ℕ)
    (ctl : StagingPhases.Calls d.load d.test d.prepare d.collect d.emit C m p ((answer m p).map Ltr.bit))
    (callee : StagingCall.Computes g q m T S)
    (width : ∀ a : EqualWords, (m a.val).length = 2*a.val.1.length)
    (correct : ∀ a : EqualWords, bitValue (m a.val) = bitValue a.val.1 * bitValue a.val.2)
    (fit : S p.u ≤ p.n) : Completed d C g q m T p := by
  have size (i : ℕ) (_ : i < p.count) : (digitReply m p i).length = 2*p.u := by
    have h := p.query_width m i
    let a : EqualWords := ⟨_, h.1.trans h.2.symm, h.1.symm ▸ p.width_pos⟩
    simpa only [a,h.1,digitReply,digitQuery] using width a
  have hz := answer_spec m correct p
  obtain ⟨t,ht,z,h,halt,out⟩ := StagingOuterOutput.run d C m p (answer m p)
    (digit d g q) StagingDigit.start ctl size
    (fun i hi => call d C m p g q T S callee i hi (size i hi) fit)
  rw [hz.1] at h ht
  refine ⟨t,ht.trans (budget C p _),z,?_,halt,out,hz⟩
  have neg : (-(radius C p.n : ℤ)) = -(StagingOuter.radius C p.n : ℤ) - ((2*p.n : ℕ):ℤ) - 1 := by
    simp [radius]; ring
  have pos : (radius C p.n : ℤ) = (StagingOuter.radius C p.n : ℤ) + ((2*p.n : ℕ):ℤ) + 1 := by
    simp [radius]
  rw [neg,pos]
  exact h

/-- The fixed controller and alphabet precede all choices of digit states,
source alphabet, digit algorithm and split exponent. -/
theorem fixed_controller :
    ∃ (d : Driver) (C : ℕ), ∀ (I Q : Type) [Fintype I] [DecidableEq I]
      (g : Rule Public.Letter Q (Index I)) (q : Q) (m : Operands → Word) (T S : ℕ → ℕ),
      StagingCall.Computes g q m T S →
      (∀ a : EqualWords, (m a.val).length = 2*a.val.1.length) →
      (∀ a : EqualWords, bitValue (m a.val) = bitValue a.val.1 * bitValue a.val.2) →
      ∀ p : ChunkTask.Input, S p.u ≤ p.n → Completed d C g q m T p := by
  obtain ⟨d,C,ctl⟩ := StagingPhases.raw_controllers
  refine ⟨d,C,?_⟩
  intro I Q _ _ g q m T S callee width correct p fits
  exact complete d C m p g q T S (ctl m p (answer_spec m correct p).1) callee width correct fits

end StagingProduct

end NearSquareRoot
end Computability
end OAI
