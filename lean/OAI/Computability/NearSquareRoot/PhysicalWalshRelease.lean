import OAI.Computability.NearSquareRoot.BoundedProgramCompile
import OAI.Computability.NearSquareRoot.ScheduleSchoolIO

/-! # Releasing a space-bounded tree program to a fixed tape machine

The final copy from the return stack to a distinct output tape takes one step
per output letter. The space limit comes from the peak compiler-stack heights
throughout the execution and covers the copy as well.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh

open IntegerMultiplication IntegerMultiplication.Code

/-- One finite machine for every input instance, with separate physical time
and visited-cell allowances. -/
def TapeRun {X : Type*} (time space : X → ℕ) (input output : X → Tree) : Prop :=
  ∃ (A Q I : Type) (_ : Finite A) (_ : Finite Q) (_ : Finite I)
    (sym : Ltr → A) (blank : A) (inp out : I) (start : Q) (m : TM.Rule A Q I),
    Function.Injective sym ∧ (∀ a, sym a ≠ blank) ∧ inp ≠ out ∧
    ∀ x, ∃ (load : I → TM.Tape A) (halt : TM.Config A Q I) (t : ℕ),
      load inp = TM.Tape.loaded blank ((input x).spell.map sym) ∧
      (∀ i, i ≠ inp → load i = TM.Tape.loaded blank []) ∧
      Trace (TM.advance m) ⟨start, load⟩ t halt ∧ TM.advance m halt = none ∧
      TM.whole blank ((output x).spell.map sym) (halt.tape out) ∧ t ≤ time x ∧
      VisitsAtMost m ⟨start, load⟩ t (space x)

theorem TapeRun.mono {X : Type*} {t s t' s' : X → ℕ} {q r : X → Tree}
    (run : TapeRun t s q r) (ht : ∀ x, t x ≤ t' x) (hs : ∀ x, s x ≤ s' x) :
    TapeRun t' s' q r := by
  obtain ⟨A,Q,I,hA,hQ,hI,sym,blank,inp,out,start,m,hi,hb,hio,good⟩ := run
  refine ⟨A,Q,I,hA,hQ,hI,sym,blank,inp,out,start,m,hi,hb,hio,fun x => ?_⟩
  obtain ⟨load,last,u,hin,hoff,tr,halt,written,clock,cells,hcard,cover⟩ := good x
  exact ⟨load,last,u,hin,hoff,tr,halt,written,clock.trans (ht x),cells,hcard.trans (hs x),cover⟩

/-- The compiler and a single constant are fixed for the entire input family. -/
def TapeTask {X : Type*} (time space : X → ℕ) (input output : X → Tree) : Prop :=
  ∃ C : ℕ, TapeRun (fun x => C*(time x+1) + (output x).count)
    (fun x => C*(space x+1)) input output

end PhysicalWalsh

namespace Space.BoundedTask

open IntegerMultiplication IntegerMultiplication.Code PhysicalWalsh

/-- The program runs with the certified stack-space bound at every prefix.
The Turing-machine clock includes draining the full result to the output tape. -/
theorem release {X : Type*} {time space : X → ℕ} {input output : X → Tree}
    (h : BoundedTask time space input output) : TapeTask time space input output := by
  obtain ⟨p,C,hp⟩ := h
  obtain ⟨A,Q,I,hA,hQ,hI,sym,blank,inp,out,start,m,K,inj,nonblank,io,exec⟩ := bounded_release p
  let D := max (2*C+1) (K*(4*C+5))
  refine ⟨D,A,Q,I,hA,hQ,hI,sym,blank,inp,out,start,m,inj,nonblank,io,fun x => ?_⟩
  obtain ⟨n,hn,run⟩ := hp x [] (fun _ => []) 0 (by intro j; rfl)
  simp only [Nat.zero_add, Schoolbook.letters_pile_empty] at run
  obtain ⟨load,last,hin,hoff,tr,halt,written,cells,hcard,cover⟩ :=
    exec (input x).spell (Schoolbook.raw (output x).spell) n _ _ run
  simp only [Schoolbook.raw_zero, Tree.spell_length, max_self] at *
  refine ⟨load,last,_,hin,hoff,tr,halt,written,?_,cells,hcard.trans ?_,cover⟩
  · have ht : (2*C+1)*(time x+1) ≤ D*(time x+1) :=
      Nat.mul_le_mul_right _ (le_max_left ..)
    rw [Nat.add_mul, Nat.mul_assoc, Nat.one_mul] at ht
    omega
  · have hc : 4*(C*(space x+1))+5 ≤ (4*C+5)*(space x+1) := by
      rw [Nat.add_mul, Nat.mul_assoc]; omega
    exact (Nat.mul_le_mul_left K hc).trans <| by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (le_max_right ..)

/-- When the time allowance covers the result length, one constant covers the
complete physical clock and the independently certified peak space. -/
theorem releaseWithin {X : Type*} {time space : X → ℕ} {input output : X → Tree}
    (h : BoundedTask time space input output) (L : ℕ)
    (hout : ∀ x, (output x).count ≤ L*(time x+1)) :
    ∃ C : ℕ, TapeRun (fun x => C*(time x+1)) (fun x => C*(space x+1)) input output := by
  obtain ⟨C,run⟩ := h.release
  refine ⟨C+L,run.mono (fun x => ?_) (fun x => ?_)⟩
  · rw [Nat.add_mul]
    exact Nat.add_le_add_left (hout x) _
  · exact Nat.mul_le_mul_right _ (Nat.le_add_right ..)

/-- Both serialized boundaries are charged to the original space budget. -/
theorem endpointSize {X : Type*} {time space : X → ℕ} {q r : X → Tree}
    (task : BoundedTask time space q r) :
    ∃ C : ℕ, ∀ x, max (q x).count (r x).count ≤ C * (space x+1) := by
  obtain ⟨_,C,h⟩ := task
  refine ⟨C, fun x => ?_⟩
  obtain ⟨_,_,run⟩ := h x [] (fun _ => []) 0 (by intro j; rfl)
  have a := run.start 0
  have b := run.finish 0
  simp only [Schoolbook.letters_pile_empty, Schoolbook.raw_zero, Tree.spell_length, Nat.zero_add]
    at a b
  exact max_le a b

/-- A time allowance dominating the arena includes the entire output copy. -/
theorem releaseOfSpaceLeTime {X : Type*} {time space : X → ℕ} {q r : X → Tree}
    (task : BoundedTask time space q r) (dom : ∀ x, space x ≤ time x) :
    ∃ C : ℕ, TapeRun (fun x => C*(time x+1)) (fun x => C*(space x+1)) q r := by
  obtain ⟨D,hD⟩ := task.endpointSize
  exact task.releaseWithin D fun x => (Nat.le_max_right _ _).trans <|
    (hD x).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (dom x) _))

end Space.BoundedTask

end NearSquareRoot
end Computability
end OAI
