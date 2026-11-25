import OAI.Computability.BorderVNP.FiniteOutputSelect

/-! # The finite-field private tape call in the team RAM

Use a single elementary bit-stack program for input loading, class selection,
native tape simulation and cleanup. The input words may have arbitrary contents.
The overhead for selecting a return class is bounded by the size of the fixed field.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldSelect

open VPVNP.RAMTape TeamPrivateTape TeamPrivateValue
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] {Q Γ : Type} {m g : ℕ}

/-- The ordinary private verifier of one numbered output class. -/
noncomputable def classCode (a : Alphabet Γ g) (digit : Bool → Γ) (i : Fin m)
    (P : TapeTable Q Γ m) (weight : Return Q Γ F m) (start : Q) (v : Fin (Fintype.card F)) :=
  TeamPrivateCompiler.code a digit i (selectTable P weight ((Fintype.equivFin F).symm v)) start

/-- The literal stack-level field-output call, including guessing the return class. -/
noncomputable def call (a : Alphabet Γ g) (digit : Bool → Γ) (i : Fin m)
    (P : TapeTable Q Γ m) (weight : Return Q Γ F m) (start : Q) :
    StackCode (TeamPrivateInput.NativePort m g) (State (Fintype.card F) (TeamPrivateCompiler.Control Q m g)) :=
  code (classCode a digit i P weight start) (.load .start)

/-- The selected field element multiplies the verified path weight at the terminal state. -/
noncomputable def callOutput : State (Fintype.card F) (TeamPrivateCompiler.Control Q m g) → F :=
  output (fun v q => if TeamPrivateCompiler.negative q then -(Fintype.equivFin F).symm v else (Fintype.equivFin F).symm v)

/-- At the concrete loading, simulation and selection budget, the compiled call returns
exactly the sum of the original field-valued multitape paths. -/
theorem call_value (a : Alphabet Γ g) (digit : Bool → Γ) (i : Fin m) (P : TapeTable Q Γ m)
    (weight : Return Q Γ F m) (start : Q) (bs : List Bool) (f ticks : ℕ)
    (stop : TapeStops P a.blank f start (input a.blank digit i bs))
    (fits : TeamPrivateInput.steps g bs + budget f (tracks a (input a.blank digit i bs)) +
      Fintype.card F ≤ ticks) :
    FieldStack.paths (call a digit i P weight start) callOutput ticks (.select (Fin.last _))
      (TeamPrivateInput.initial bs) = tapeValue P a.blank weight f start (input a.blank digit i bs) := by
  let bound := TeamPrivateInput.steps g bs + budget f (tracks a (input a.blank digit i bs))
  let val (j : Fin (Fintype.card F)) : F :=
    (tapePaths (selectTable P weight ((Fintype.equivFin F).symm j)) a.blank f start (input a.blank digit i bs) : F) *
      (Fintype.equivFin F).symm j
  have he (j) (t : ℕ) (ht : bound ≤ t) :
      FieldStack.paths (classCode a digit i P weight start j)
        (fun q => if TeamPrivateCompiler.negative q then -(Fintype.equivFin F).symm j else (Fintype.equivFin F).symm j)
        t (.load .start) (TeamPrivateInput.initial bs) = val j := by
    rw [signed_scalar]
    have hs := (stops_iff P a.blank weight f start (input a.blank digit i bs) ((Fintype.equivFin F).symm j)).mpr stop
    unfold classCode val
    rw [(input_value a digit i (selectTable P weight ((Fintype.equivFin F).symm j)) start bs f hs t ht).2]
  calc
    _ = ∑ j, val j := selection_value _ _ _ _ val bound he (Fintype.card F) le_rfl ticks fits
    _ = _ := by rw [tapeValue_eq_select]; exact (Fintype.equivFin F).symm.sum_comp (fun v => (tapePaths (selectTable P weight v) a.blank f start (input a.blank digit i bs) : F) * v)

end FieldSelect

end BorderVNP
end Computability
end OAI
