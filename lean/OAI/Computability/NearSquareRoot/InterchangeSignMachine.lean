import OAI.Computability.IntegerMultiplication.Interface
import OAI.Computability.NearSquareRoot.InterchangeSignRuns
import OAI.Computability.NearSquareRoot.InterchangeSplitVisits

/-! # Physical realization of the comparison stream

The general release lemma retains the original linear allowance when copying
an encoded reply from the return stack to the output tape.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open IntegerMultiplication Code

/-- One deterministic machine for all inputs. Resources include loading the
private stacks and draining the entire output to its conventional tape. -/
def LinearTreeMachine {X : Type*} (budget : X → ℕ) (input output : X → Tree) : Prop :=
  ∃ (A Q I : Type) (_ : Finite A) (_ : Finite Q) (_ : Finite I)
      (sym : Ltr → A) (blank : A) (inp out : I) (start : Q) (m : TM.Rule A Q I) (C : ℕ),
    Function.Injective sym ∧ (∀ a, sym a ≠ blank) ∧ inp ≠ out ∧
    ∀ x, ∃ (init : I → TM.Tape A) (last : TM.Config A Q I) (t : ℕ),
      init inp = TM.Tape.loaded blank ((input x).spell.map sym) ∧
      (∀ i, i ≠ inp → init i = TM.Tape.loaded blank []) ∧
      Trace (TM.advance m) ⟨start, init⟩ t last ∧ TM.advance m last = none ∧
      TM.whole blank ((output x).spell.map sym) (last.tape out) ∧
      t ≤ C * budget x ∧ VisitsAtMost m ⟨start, init⟩ t (C * budget x)

/-- Realize a budgeted program with serialized input and output trees. -/
theorem linearTreeMachine_of_carries {X : Type*} {budget : X → ℕ} {input output : X → Tree}
    (h : Carries (fun x => (budget x : ℝ)) input output) : LinearTreeMachine budget input output := by
  classical
  obtain ⟨D, hd⟩ := h.out
  obtain ⟨hpos, b, ⟨cmd, C, run⟩, K, hk⟩ := h.runs
  obtain ⟨A, Q, I, hA, hQ, hI, sym, blank, inp, out, hinj, start, m, hsym, hblank, hrelease⟩ :=
    Prog.release cmd
  let : Fintype I := Fintype.ofFinite I
  let L := 2*C*K + D + 1
  refine ⟨A, Q, I, hA, hQ, hI, sym, blank, inp, out, start, m, (Fintype.card I + 1) * (L + 1),
    hsym, hblank, hinj, fun x => ?_⟩
  obtain ⟨t, ht, hr⟩ := run x [] (fun _ => [])
  have frame (z : Tree) : letters (pile 0 z (fun _ => [])) = fun i => if i=0 then z.spell else [] := by
    funext i
    by_cases hi : i = 0
    · subst i; simp [letters]
    · simp [letters, hi]
  rw [frame, frame] at hr
  obtain ⟨last, init, hin, hrest, trace, halt, hout⟩ := hrelease _ _ _ hr
  simp only [↓reduceIte, Tree.spell_length] at trace hout
  have h₁ : 1 ≤ budget x := by exact_mod_cast (show (1:ℝ) ≤ budget x from hpos x)
  have h₂ : b x + 1 ≤ K * budget x := by exact_mod_cast (show (b x : ℝ) + 1 ≤ (K : ℝ) * budget x from hk x)
  have h₃ : (output x).count ≤ D * budget x := by exact_mod_cast (show ((output x).count : ℝ) ≤ (D : ℝ) * budget x from hd x)
  have h₄ : t ≤ C * (K * budget x) := ht.trans (Nat.mul_le_mul_left _ h₂)
  let steps := 2*t + 1 + (output x).count
  have hsteps : steps ≤ L * budget x := by
    dsimp only [steps, L]; nlinarith
  have hsucc : steps + 1 ≤ (L + 1) * budget x := by nlinarith
  have hfinal : steps ≤ (Fintype.card I + 1) * (L + 1) * budget x := by
    calc
      steps ≤ (L + 1) * budget x := (Nat.le_succ _).trans hsucc
      _ ≤ (Fintype.card I + 1) * (L + 1) * budget x := by nlinarith
  obtain ⟨cells, hcard, hall⟩ := visitsAtMost_of_step_count m ⟨start, init⟩ steps
  refine ⟨init, last, steps, hin, hrest, trace, halt, hout, hfinal, cells, hcard.trans ?_, hall⟩
  calc
    _ ≤ Fintype.card I * ((L+1) * budget x) := Nat.mul_le_mul_left _ hsucc
    _ ≤ (Fintype.card I + 1) * (L+1) * budget x := by nlinarith

/-- The spectral comparison tags for one suffix fibre are produced in linear
physical time and space, uniformly in the binary dimensions. -/
theorem InterchangeSignRuns.comparison_machine {A : Type} [Codec A] (before equal after : A) :
    LinearTreeMachine (fun f : InterchangeSignRuns.Fibre => f.d * f.s)
      (fun f => send (InterchangeSignRuns.header f))
      (fun f => send (InterchangeSignRuns.tags before equal after f)) :=
  linearTreeMachine_of_carries (InterchangeSignRuns.comparison_program before equal after)

end NearSquareRoot
end Computability
end OAI
