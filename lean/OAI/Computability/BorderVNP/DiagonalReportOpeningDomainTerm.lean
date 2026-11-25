import Lean

/-! # Quantifying the returned team histories of a report opener -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term

/-- Bind the operands of a physical opening test and name its proposition at those
operands. This retains the original dependent types when the opening is available
only at one exterior, ownership scan and report return. -/
syntax "atReportOpening% " term:max " with " ident+ " as " ident " => " term : term

elab_rules : term
  | `(atReportOpening% $test with $ids:ident* as $atReturn => $body) => do
    let opening ← elabTerm test (some (mkSort .zero))
    let rec bind (index : Nat) (current : Expr) : TermElabM Expr := do
      if h : index < ids.size then
        let .forallE _ domain tail info ← whnf current | throwError "expected a physical opening operand"
        withLocalDecl ids[index].getId info domain fun value => do
          let result ← bind (index+1) (tail.instantiate1 value)
          mkLambdaFVars #[value] result
      else
        withLetDecl atReturn.getId (mkSort .zero) current fun point => do
          let result ← elabTerm body none
          mkLetFVars #[point] result
    bind 0 opening

end Diagonal

end BorderVNP
end Computability
end OAI
