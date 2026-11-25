import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxPackOutput

/-! # Packed numerical transition rows for the structured-program compiler -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Pack

open IntegerMultiplication CommonAlphabet Transition

/-- The input pair contains a state number and a packed tuple of register tops. -/
def sourceRow (aSize : ℕ) (opts : List (Option ℕ)) (sites : List Site) (adr : ℕ × ℕ) :
    Option (ℕ × ℕ) :=
  output aSize sites (step opts sites (heads aSize sites adr.2) (decodePC sites adr.1))

/-- All complete and partial source units have the same numerical row semantics
as the P192 compiler, including returns, absent targets and unchanged stacks. -/
theorem sources {A : Type} [Fintype A] (a : Numbering A) (U : List (Prog.Loc A)) :
    Generator.StackRows.Sources (symbols a U) (pcs a U) (Pack.stacks U) (Prog.compile U)
      (sourceRow a.size (options (letter a)) (U.map (site (letter a)))) := by
  intro q top
  unfold sourceRow
  rw [decodePC_eq]
  apply output_correct
  intro j
  apply step_correct
  exact heads_eq a U top

end GeneratorSyntax.Pack

end NearSquareRoot
end Computability
end OAI
