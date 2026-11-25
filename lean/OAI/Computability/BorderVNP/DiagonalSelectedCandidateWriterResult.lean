import OAI.Computability.BorderVNP.DiagonalSelectedCandidateWriterLabel

/-! # The result type of the selected physical writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open Lean Meta Elab Term

private def lookupLevels : List Level := [Level.param `u_1, Level.param `u_2, Level.param `u_3]

local elab "selectedPhysicalTypeFamily%" : term => do
  let old := Lean.mkConst ``selectedLookupOfCandidateWriters lookupLevels
  forallTelescope (← inferType old) fun args result => mkLambdaFVars args result

/-- The returned sites on the very wire and frame selected by the positive
candidate writer. Its parameters are those of `selectedLookupOfCandidateWriters`. -/
noncomputable def selectedPhysicalWriterType.{u_1,u_2,u_3} := selectedPhysicalTypeFamily%

local elab "selectedPhysicalSignature%" : term => do
  let old := Lean.mkConst ``selectedLookupOfCandidateWriters lookupLevels
  let family := Lean.mkConst ``selectedPhysicalWriterType lookupLevels
  forallTelescope (← inferType old) fun args _ => mkForallFVars args (mkAppN family args)

/-- The original writer selection, with its dependent return type named before
specializing to a calendar. -/
noncomputable def selectedPhysicalWriter.{u_1,u_2,u_3} : selectedPhysicalSignature% :=
  @selectedLookupOfCandidateWriters.{u_1,u_2,u_3}

/-- Keep the selected result type as an application of the named type family
when the physical arguments are specialized. -/
elab "namedPhysicalLookup%" actual:term:max : term => do
  let old ← elabTerm actual none
  unless old.isAppOf ``selectedLookupOfCandidateWriters do throwError "expected the selected physical writer"
  return mkAppN (Lean.mkConst ``selectedPhysicalWriter old.getAppFn.constLevels!) old.getAppArgs

end TeamContraction

end BorderVNP
end Computability
end OAI
