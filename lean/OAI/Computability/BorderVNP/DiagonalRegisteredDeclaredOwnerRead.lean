import OAI.Computability.BorderVNP.DiagonalSelectedDeclaredOwnerRead
import OAI.Computability.BorderVNP.DiagonalPublishedOwnerRead
import OAI.Computability.BorderVNP.DiagonalIssuedEnumerations

/-! # Declared owner words at a supplied selected lookup

The selected lookup already fixes the network, enumerations, broadcast and
preparation frame. Apply the owner read with those same parameters and then
use the lookup's own writer projection to read the configured team.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open Lean Meta Elab Term RoutingISA.Evaluator.SignedPrep

private def declaredReadOnSelected (selected : Expr) (word : Option Syntax)
    (route declaration : Syntax) : TermElabM Expr := do
  let some record ← whnfUntil (← inferType selected) ``PreparationFrame.SelectedLookupSites |
    throwError "expected the selected lookup on its preparation frame"
  let lemmaInfo ← getConstInfo ``PreparationFrame.SelectedLookupSites.ownerOnDeclaredCell
  let levels := record.getAppFn.constLevels!.take lemmaInfo.levelParams.length
  let read := mkAppN (mkConst lemmaInfo.name levels) (record.getAppArgs.push selected)
  let storedType := (← whnf (← inferType read)).bindingDomain!
  let stored ← match word with
    | some witness => elabTermEnsuringType witness storedType
    | none => forallTelescope storedType fun cell equality => do
      let some (_, value, _) := equality.eq? | throwError "expected the declared team's stored owner word"
      mkLambdaFVars cell (← mkEqRefl value)
  let native ← elabTerm route none
  let advertised ← elabTerm declaration none
  return mkAppN read #[stored, native, advertised]

/-- Read the declared owner at every cell of the supplied route using the
configured native word or an explicit proof of its value. -/
syntax "selectedDeclaredOwner% " term:max " on " term:max " matching " term:max (ppSpace "given " term:max)? : term

elab_rules : term
  | `(selectedDeclaredOwner% $s on $q matching $d given $w) => withoutErrToSorry do
    declaredReadOnSelected (← elabTerm s none) (some w) q d
  | `(selectedDeclaredOwner% $s on $q matching $d) => withoutErrToSorry do
    declaredReadOnSelected (← elabTerm s none) none q d

/-- Read the receiving team's word through the projection of the same registered lookup.
The optional witness supplies the native owner at each cell. The calendar installs
this declared word definitionally. -/
syntax "registeredOwnerWords% " term:max " on " term:max " matching " term:max (ppSpace "given " term:max)? : term

macro_rules
  | `(registeredOwnerWords% $s on $q matching $d given $w) => do
    let owned := mkIdent `owned
    let projection := mkIdent `projection
    `(publishedOwnerRead% (selectedDeclaredOwner% $s on $q matching $d given $w)
        via (issuedField% $owned (issuedField% $projection $s)))
  | `(registeredOwnerWords% $s on $q matching $d) => do
    let owned := mkIdent `owned
    let projection := mkIdent `projection
    `(publishedOwnerRead% (selectedDeclaredOwner% $s on $q matching $d)
        via (issuedField% $owned (issuedField% $projection $s)))

open Lean.Elab.Command in
run_cmd liftTermElabM do
  let prior ← getConstInfo ``PreparationFrame.SelectedLookupSites.ownerOnDeclaredCell
  let proof ← forallTelescope prior.type fun inputs _ => do
    let (site, written, route, declaration) := (inputs[inputs.size-5]!, inputs[inputs.size-4]!,
      inputs[inputs.size-3]!, inputs[inputs.size-2]!)
    let s ← exprToSyntax site
    let w ← exprToSyntax written
    let q ← exprToSyntax route
    let d ← exprToSyntax declaration
    let read ← withoutErrToSorry <| elabTerm (← `(registeredOwnerWords% $s on $q matching $d given $w)) none
    mkLambdaFVars (inputs.extract 0 (inputs.size-1)) (← instantiateMVars read)
  let name := `OAI.Computability.BorderVNP.TeamContraction.PreparationFrame.SelectedLookupSites.publishedOwnerOnDeclaredCell
  addDecl (.thmDecl { name := name, levelParams := prior.levelParams, type := ← inferType proof, value := proof })
  addDocStringCore name "On each matching route, every cell reads the configured owner's receiving-team word through the writer of its own selected lookup."

end TeamContraction

end BorderVNP
end Computability
end OAI
