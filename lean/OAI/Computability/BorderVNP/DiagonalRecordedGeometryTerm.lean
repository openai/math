import OAI.Computability.BorderVNP.DiagonalCalendarNativeRegisteredGeometry

/-! # The planner geometry application at an issued native site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open PackedHistoryCircuit
open Lean Meta Elab Term

private def receiptParameters (record : Expr) (head : Name) : TermElabM (NameMap Expr) := do
  let some app ← whnfUntil (← inferType record) head | throwError "expected native receipt {head}"
  let info ← getConstInfo head
  forallTelescope info.type fun xs _ => do
    let mut vals : NameMap Expr := {}
    for x in xs, value in app.getAppArgs do vals := vals.insert (← x.fvarId!.getUserName) value
    return vals

/-- Construct the calibrated geometry expression from the indices carried by
the original residence, pin and returned site. -/
elab (name := instantiatedPlannerGeometry) "geometryFromNative%" siteTask:term:max routing:term:max values:term:max hist:term:max team:term:max
    boot:term:max pin:term:max packet:term:max on:term:max : term => do
  let fixed ← elabTerm siteTask none
  let routing ← elabTerm routing none
  let table ← elabTerm values none
  let hist ← elabTerm hist none
  let u ← elabTerm team none
  let boot ← elabTerm boot none
  let pin ← elabTerm pin none
  let image ← elabTerm packet none
  let on ← elabTerm on none
  let b ← receiptParameters boot ``BootResidence
  let p ← receiptParameters pin ``PublishedPin
  let mut terms : NameMap Expr := {}
  for (name,field) in [(`k,`k),(`pf,`F),(`bf,`f),(`advice,`A),(`lib,`mac),(`hdr,`bits),
      (`init,`initial),(`bank,`bank),(`g,`guess),(`after,`after)] do
    let some x := b.find? field | throwError "missing native boot field {field}"
    terms := terms.insert name x
  for (name,field) in [(`mem,`pinMem),(`post,`postPin),(`regs,`preRegs),(`used,`usedPin),(`cost,`profCost)] do
    let some x := p.find? field | throwError "missing native pin field {field}"
    terms := terms.insert name x
  for (name,field,left) in [(`hreg,`geometryRegs,`retained),(`hmem,`geometryMemory,`seen),
      (`hused,`pinCost,`attained),(`hcost,`geometryCost,`charged)] do
    let proof ← mkProjection on field
    let some sides ← whnfUntil (← inferType proof) ``Eq | throwError "expected the native endpoint equality {field}"
    terms := terms.insert name proof |>.insert left sides.getAppArgs[1]!
  terms := terms.insert `resident boot |>.insert `published pin |>.insert `packet image
  let fn := ``SignedCalendarAt.frozenPlannerGeometryOnPin
  let info ← getConstInfo fn
  forallTelescope info.type fun xs _ => do
    let mut args := fixed.getAppArgs ++ #[routing,table,hist,u]
    let first ← xs[args.size]!.fvarId!.getUserName
    unless first == `k do throwError "unexpected first issued geometry parameter {first}"
    for x in xs.extract args.size xs.size do
      let name ← x.fvarId!.getUserName
      let some value := terms.find? name | throwError "missing actual geometry input {name}"
      args := args.push value
    return mkAppN (Lean.mkConst fn fixed.getAppFn.constLevels!) args

end Diagonal

end BorderVNP
end Computability
end OAI
