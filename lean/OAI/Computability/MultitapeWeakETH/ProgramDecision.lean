import OAI.Computability.MultitapeWeakETH.StackDecision
import OAI.Computability.IntegerMultiplication.Prog.Compile

/-! # A fixed recursive register program decides on the Weak ETH tapes -/

namespace OAI.Computability.MultitapeWeakETH.DecisionTapes

open DepthThreeLowerBound IntegerMultiplication
open scoped Classical
noncomputable section

/-- Transfer charged program executions on raw binary input to a single
machine. On return the Boolean answer is a function of the first output
symbol, with the empty output handled by the same function. -/
theorem compile_program {A : Type} [Fintype A] (p : Prog A) (letter : Bool → A)
    (inj : Function.Injective letter) (answer : Option A → Bool) :
    ∃ M : FiniteMultiTapeMachine, ∀ (bits : List Bool) (n : ℕ) (r : Reg A),
      Prog.Run [] p (fun i => if i=0 then bits.map letter else []) n r →
      MultiTapeHaltsIn M bits (answer (r 0).head?) (2*n+1) := by
  let U := Prog.sites [] p
  let _ : Fintype (Prog.Ptr U) := Fintype.subtype U.toFinset (by simp)
  let _ : Fintype (Prog.Idx U) := Fintype.subtype (Prog.used U).toFinset (by simp)
  let reg : Prog.Idx U := ⟨0,by simp [Prog.used]⟩
  let initial : Prog.Pc U := if h : ([],p) ∈ U then some ⟨([],p),h⟩ else none
  let bit (b : Bool) : Prog.Sym U := .inl (letter b)
  let decode (z : Option (Prog.Sym U)) := z.bind fun a => a.elim some (fun _ => none)
  let read (_ : Prog.Pc U) (top : Prog.Ix U → Option (Prog.Sym U)) := answer (decode (top (some reg)))
  obtain ⟨M,works⟩ := compile_stack (Prog.compile U) initial (some reg) bit
    (fun _ _ h => inj (Sum.inl.inj h)) read
  refine ⟨M,?_⟩
  intro bits n r run
  have path := Prog.Run.compile_ok U run (fun _ h => h) (fun i => by simp) []
  let raw (i : ℕ) := if i=0 then bits.map letter else []
  have init : Prog.machine U initial raw [] = SM.origin initial (some reg) (bits.map bit) := by
    unfold Prog.machine SM.origin
    congr 1
    funext i
    cases i with
    | none => rfl
    | some j =>
      by_cases h : j=reg
      · subst j; simp [raw,reg,bit,List.map_map,Function.comp_def]
      · have ne : j.val ≠ 0 := fun eq => h (Subtype.ext eq)
        simp [raw,ne,h]
  change Trace _ (Prog.machine U initial raw []) _ _ at path
  rw [init] at path
  have result := works bits n (Prog.machine U none r []) path rfl
  convert! result using 2
  change (r 0).head? = decode ((r 0).map Sum.inl).head?
  cases r 0 <;> rfl

end
end OAI.Computability.MultitapeWeakETH.DecisionTapes
