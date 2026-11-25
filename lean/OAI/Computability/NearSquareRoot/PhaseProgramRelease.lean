import OAI.Computability.IntegerMultiplication.Code.CodePolyBasic
import OAI.Computability.IntegerMultiplication.Interface
import OAI.Computability.NearSquareRoot.InterchangeSplitVisits

/-! # Physical cost of encoded-tree parameter generation

The compiler's cost includes the final scan transferring the answer to a dedicated
output tape. The output length is polynomial by the stack program's length theorem.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open IntegerMultiplication Code

/-- A fixed finite-tape machine reads the spelling of a query tree and halts with
exactly the spelling of the reply tree on a distinct output tape. The same
polynomial bounds the execution time and the number of visited tape cells. -/
def PolyTreeMachine {X : Type*} (scale : X → ℕ) (query reply : X → Tree) : Prop :=
  ∃ (A Q I : Type) (_ : Finite A) (_ : Finite Q) (_ : Finite I)
    (sym : Ltr → A) (blank : A) (inp out : I) (start : Q) (m : TM.Rule A Q I)
    (degree coeff : ℕ),
    Function.Injective sym ∧ (∀ a, sym a ≠ blank) ∧ inp ≠ out ∧
    ∀ x, ∃ (init : I → TM.Tape A) (finish : TM.Config A Q I) (t : ℕ),
      init inp = TM.Tape.loaded blank ((query x).spell.map sym) ∧
      (∀ i, i ≠ inp → init i = TM.Tape.loaded blank []) ∧
      Trace (TM.advance m) ⟨start, init⟩ t finish ∧ TM.advance m finish = none ∧
      TM.whole blank ((reply x).spell.map sym) (finish.tape out) ∧
      t ≤ coeff * (scale x + 1) ^ degree ∧
      VisitsAtMost m ⟨start, init⟩ t (coeff * (scale x + 1) ^ degree)

private theorem singleton_deck_letters (x : Tree) :
    letters (pile 0 x (fun _ => [])) = fun i => if i = 0 then x.spell else [] := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [letters]
  · simp [letters, hi]

/-- Release a polynomial stack task on its encoded inputs as a finite multitape machine. -/
theorem polyTreeMachine_of_BT {X : Type*} {scale : X → ℕ} {query reply : X → Tree}
    (h : Task.BT scale query reply) (hquery : Dom scale (fun x => (query x).count)) :
    PolyTreeMachine scale query reply := by
  classical
  have hreply := h.length hquery
  obtain ⟨b, hb, prog, C, run⟩ := h
  obtain ⟨A, Q, I, hA, hQ, hI, sym, blank, inp, out, distinct, start, m,
    injective, nonblank, release⟩ := Prog.release prog
  let : Fintype I := Fintype.ofFinite I
  let bound x := 2 * C * (b x + 1) + 1 + (reply x).count
  have poly : Dom scale bound :=
    (((Dom.const scale (2 * C)).mul (hb.add (.const scale 1))).add (.const scale 1)).add hreply
  obtain ⟨degree, coeff, majorize⟩ := poly.add
    ((Dom.const scale (Fintype.card I)).mul (poly.add (.const scale 1)))
  refine ⟨A, Q, I, hA, hQ, hI, sym, blank, inp, out, start, m, degree, coeff,
    injective, nonblank, distinct, fun x => ?_⟩
  obtain ⟨t, ht, hrun⟩ := run x [] (fun _ => [])
  rw [singleton_deck_letters, singleton_deck_letters] at hrun
  obtain ⟨finish, init, hin, hothers, htrace, hhalt, hout⟩ := release _ _ _ hrun
  simp only [↓reduceIte, Tree.spell_length] at htrace hout
  have hcost : 2 * t + 1 + (reply x).count ≤ bound x := by
    unfold bound
    simpa only [Nat.mul_assoc] using Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 ht) 1) (reply x).count
  have hmajor := majorize x
  change bound x + Fintype.card I * (bound x + 1) ≤ _ at hmajor
  obtain ⟨visited, hcard, hvisit⟩ := visitsAtMost_of_step_count m ⟨start, init⟩
    (2 * t + 1 + (reply x).count)
  refine ⟨init, finish, _, hin, hothers, htrace, hhalt, hout, by omega, visited, ?_, hvisit⟩
  exact hcard.trans ((Nat.mul_le_mul_left _ (Nat.succ_le_succ hcost)).trans
    ((Nat.le_add_left _ _).trans hmajor))

end NearSquareRoot
end Computability
end OAI
