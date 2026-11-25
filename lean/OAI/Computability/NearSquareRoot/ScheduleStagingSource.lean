import OAI.Computability.NearSquareRoot.ScheduleStagingCall
import OAI.Computability.NearSquareRoot.CommonAlphabetIOPipelineSource

/-! # Converting a source digit rule only at the short-multiplication boundary -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingSource

open IntegerMultiplication TM CommonAlphabet CommonAlphabet.Pipeline Bits
open ChunkLoop ChunkTask

variable {A Q I : Type} [DecidableEq I] [Fintype I]

/-- Conventional raw input, an exact whole output, and resource bounds of
the finite source machine before changing its alphabet. -/
def Computes (m : Rule A Q I) (q : Q) (blank sep : A) (bit : Bool → A) (inp out : I)
    (f : Operands → Word) (T S : ℕ → ℕ) : Prop :=
  ∀ a : EqualWords,
    let init := loadedConfig q blank (sourceLoad bit sep inp a.val.1 a.val.2)
    ∃ t ≤ T a.val.1.length, ∃ z, Trace (advance m) init t z ∧ advance m z = none ∧
      whole blank ((f a.val).map bit) (z.tape out) ∧ VisitsAtMost m init t (S a.val.1.length)

/-- Both constants may depend on the *digit* alphabet. Only its local
operands, run and workspace pay those factors. -/
theorem computes (c : CommonAlphabet.Code A) (bit : Bool → A) (sep blank : A)
    (hb : c.enc blank = fun _ => none) (decode : A → Option Bool)
    (empty : decode blank = none) (digits : ∀ b, decode (bit b) = some b)
    (inp out : I) (m : Rule A Q I) (q : Q) (f : Operands → Word) (T S : ℕ → ℕ)
    (source : Computes m q blank sep bit inp out f T S)
    (width : ∀ a : EqualWords, (f a.val).length = 2*a.val.1.length) :
    let H := Fintype.card (Index (Option I))
    StagingCall.Computes (sourceMachine c bit sep decode inp out m q) (sourceEntry A Q I c.width) f
      (fun u => 32*(c.width+1)*(T u+u+1))
      (fun u => (48*(c.width+1)+3*H)*(S u+u+1)) := by
  dsimp only
  intro a
  obtain ⟨t,ht,z,path,halt,word,space⟩ := source a
  obtain ⟨ticks,stop,clocked,run,done,outWord,visited⟩ := literal_from_source c bit sep blank hb
    decode empty digits inp out m q a.val.1 a.val.2 (f a.val) z path halt word space
  have lengths : a.val.1.length = a.val.2.length := a.property.1
  have hw := width a
  let u := a.val.1.length
  let H := Fintype.card (Index (Option I))
  refine ⟨ticks,clocked.trans ?_,stop,run,done,outWord,?_⟩
  · simp only [expandSteps,compactSteps,clock,hw,← lengths]
    have h := Nat.mul_le_mul_left (1+5*c.width) ht
    nlinarith
  · obtain ⟨cells,cap,cover⟩ := visited
    refine ⟨cells,cap.trans ?_,cover⟩
    simp only [expandSteps,compactSteps,hw,← lengths]
    change _ ≤ (48*(c.width+1)+3*H)*(S u+u+1)
    change 2*(2*(c.width+1)*(u+1+u)+2+1)+H+
      (2*((2*(1+5*c.width)+1)*S u)+H)+(2*(2*((c.width+1)*(2*u+1))+1)+H) ≤ _
    nlinarith

end StagingSource

end NearSquareRoot
end Computability
end OAI
