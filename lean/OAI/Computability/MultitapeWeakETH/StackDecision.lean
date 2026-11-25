import OAI.Computability.MultitapeWeakETH.DecisionTapes
import OAI.Computability.IntegerMultiplication.SM.Output

/-! # Boolean decisions on finite stacks compiled to the Weak ETH tape clock -/

namespace OAI.Computability.MultitapeWeakETH.DecisionTapes

open DepthThreeLowerBound IntegerMultiplication
open scoped Classical
noncomputable section

variable {A Q I : Type}

/-- Inspect the scanned symbols on the first halt and retain the answer in
one of two final control states. -/
def observe (rule : TM.Rule A Q I) (answer : Q → (I → A) → Bool) : TM.Rule A (Q ⊕ Bool) I
  | .inr _, _ => none
  | .inl q, top =>
    match rule q top with
    | some (p,op) => some (.inl p,op)
    | none => some (.inr (answer q top),fun i => (top i,.stay))

private def live (x : TM.Config A Q I) : TM.Config A (Q ⊕ Bool) I := ⟨.inl x.pc,x.tape⟩

theorem observe_trace (rule : TM.Rule A Q I) (answer : Q → (I → A) → Bool)
    {x y : TM.Config A Q I} {n : ℕ} (h : Trace (TM.advance rule) x n y) :
    Trace (TM.advance (observe rule answer)) (live x) n (live y) := by
  induction h with
  | nil => exact .nil _
  | @cons x y z n step _ ih =>
    apply Trace.cons _ ih
    obtain ⟨⟨q,op⟩,entry,hy⟩ := Option.map_eq_some_iff.mp step
    subst y
    simp [TM.advance,observe,live,entry]

theorem observe_halt (rule : TM.Rule A Q I) (answer : Q → (I → A) → Bool)
    (x : TM.Config A Q I) (hh : TM.advance rule x = none) :
    ∃ y, Trace (TM.advance (observe rule answer)) (live x) 1 y ∧
      TM.advance (observe rule answer) y = none ∧ y.pc = .inr (answer x.pc (fun i => (x.tape i).view 0)) := by
  have h := Option.map_eq_none_iff.mp hh
  let final : TM.Config A (Q ⊕ Bool) I := ⟨.inr (answer x.pc (fun i => (x.tape i).view 0)),
    fun i => (x.tape i).apply ((x.tape i).view 0,.stay)⟩
  refine ⟨final,Trace.single ?_,rfl,rfl⟩
  simp [TM.advance,live,observe,h,final]

/-- One fixed stack program, with acceptance tested from its final pc and
stack tops, gives one physical machine on raw binary input. Its clock is
twice the stack clock plus one transition to record the answer. -/
theorem compile_stack [Finite A] [Finite Q] [Finite I] [DecidableEq I]
    (rule : SM.Rule A Q I) (initial : Q) (input : I)
    (letter : Bool → A) (inj : Function.Injective letter) (answer : Q → (I → Option A) → Bool) :
    ∃ M : FiniteMultiTapeMachine, ∀ (bits : List Bool) (n : ℕ) (x : SM.Config A Q I),
      Trace (SM.advance rule) (SM.origin initial input (bits.map letter)) n x →
      SM.advance rule x = none → MultiTapeHaltsIn M bits (answer x.pc (SM.tops x)) (2*n+1) := by
  let _ : Inhabited (Option A) := ⟨none⟩
  let _ : Fintype A := Fintype.ofFinite _
  let _ : Fintype Q := Fintype.ofFinite _
  let _ : Fintype I := Fintype.ofFinite _
  let check (q : SM.PC A Q I) (top : I → Option A) := q.elim (fun p => answer p top) (fun _ => false)
  let prog := observe (SM.toTM rule) check
  let pc : SM.PC A Q I ⊕ Bool := .inl (.inl initial)
  let symbol := Option.some ∘ letter
  have hi : Function.Injective symbol := fun _ _ eq => inj (Option.some.inj eq)
  have mark (b) : symbol b ≠ default := Option.some_ne_none _
  let accept (q : SM.PC A Q I ⊕ Bool) := q.elim (fun _ => false) id
  let _ : Fintype (SM.PC A Q I ⊕ Bool) := Fintype.ofFinite _
  refine ⟨machine prog input symbol hi mark pc accept,?_⟩
  intro bits n x run stop
  let tapes := (start input symbol (Sum.inl initial : SM.PC A Q I) bits).tape
  have faithful : SM.faithful (SM.origin initial input (bits.map letter)).stack tapes := by
    intro i
    by_cases eq : i = input
    · simpa [tapes,start,SM.origin,eq,symbol,List.map_map,show (default : Option A) = none from rfl] using SM.display_loaded (bits.map letter)
    · simpa [tapes,start,SM.origin,eq,show (default : Option A) = none from rfl] using SM.display_loaded ([] : List A)
  obtain ⟨endTape,faithful',physical⟩ := SM.simulate run tapes faithful
  have stopped := SM.simulate_halt stop faithful'
  obtain ⟨final,last,halt,flag⟩ := observe_halt (SM.toTM rule) check _ stopped
  have obs := (observe_trace _ check physical).trans last
  have head : (fun i => (endTape i).view 0) = SM.tops x := by
    funext i; rw [faithful' i,SM.display_top]; rfl
  have correct : accept final.pc = answer x.pc (SM.tops x) := by
    rw [flag]; change answer x.pc _ = _; rw [head]
  exact correct ▸ haltsIn prog input symbol hi mark pc accept bits obs halt

end
end OAI.Computability.MultitapeWeakETH.DecisionTapes
