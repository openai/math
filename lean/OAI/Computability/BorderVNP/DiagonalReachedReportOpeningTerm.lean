import OAI.Computability.BorderVNP.DiagonalFrozenControlReportAllocation

/-! # Reading the actual opening and seed before a signed report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term TeamContraction

/-- Abstract the return values using the actual opening test's own
telescope, and keep its reached proof at those very arguments. -/
syntax "onPhysicalReportOpening% " term:max " with " ident+ " as " ident " => " term : term

elab_rules : term
  | `(onPhysicalReportOpening% $op with $ids:ident* as $received => $body) => do
    let checked ← elabTerm op none
    let rec take (i : Nat) (ty op : Expr) : TermElabM Expr := do
      if h : i < ids.size then
        let .forallE _ dom cod bi ← whnf ty | throwError "expected the next opening operand"
        withLocalDecl ids[i].getId bi dom fun v => do
          let term ← take (i+1) (cod.instantiate1 v) (mkApp op v)
          mkLambdaFVars #[v] term
      else
        withLetDecl received.getId ty op fun v => do
          let term ← elabTerm body none
          mkLetFVars #[v] term
    take 0 (← inferType checked) checked

private def physicalHead (ty : Expr) (c : Name) : MetaM Expr := do
  let some head ← whnfUntil ty c | throwError "expected {c} at the prepared report"
  return head

/-- Use the parameter values of a concrete reached control entry, matched
rows, control return, and report seed directly in the source bank proof. -/
syntax "physicalReportBank% " term:max term:max term:max term:max term:max term:max term:max : term

elab_rules : term
  | `(physicalReportBank% $entry $axis $same $advance $report $seed $alloc) => do
    let values ← #[entry,axis,same,advance,report,seed,alloc].mapM fun s => elabTerm s none
    let names := #[`entry,`axis,`same,`advance,`_report,`seed,`alloc]
    let op ← getConstInfo ``FrozenControlEntry.reportAllocationAtReturn
    forallTelescope op.type fun params _ => do
      let mut args := #[]
      for p in params do
        let name ← p.fvarId!.getUserName
        if let some i := names.idxOf? name then
          let v := values[i]!
          args := args.push (p.fvarId!,v)
          if [`entry,`same,`advance,`seed].contains name then
            let pattern ← inferType p
            let head := pattern.getAppFn.constName?.get!
            let real ← physicalHead (← inferType v) head
            for (f,a) in pattern.getAppArgs.zip real.getAppArgs do
              if f.isFVar then args := args.push (f.fvarId!,a)
      let mut result := Lean.mkConst op.name
      for p in params do
        let some (_,v) := args.find? (·.1 == p.fvarId!)
          | throwError "the observed native inputs leave {← p.fvarId!.getUserName} unavailable"
        result := mkApp result v
      return result

end Diagonal

end BorderVNP
end Computability
end OAI
