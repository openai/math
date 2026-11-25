import OAI.Computability.BorderVNP.DiagonalCandidateLibraryReturn
import OAI.Computability.BorderVNP.DiagonalCandidateLayoutReturn

/-! # The same candidate return on the planner layout and library -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM TeamContraction JointHeader Packing BorderVNP.Cube Physical LocalRow
open PackedHistoryCircuit Crossing

variable {w R X : ℕ} {ar : CubeArena.Layout} {D : Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {word : Broadcast ar.n ar.header.d ar.header.cap} {owner : ℕ → Fin (R+1)}
    {decl : LengthDeclaration ar.n ar.header.d} {group : Fin ar.header.d → Fin (R+1)}
    {frame base : ℕ} {pins : Pins.Layout} {fields : Pins.ProcessorFields pins} {f : BroadcastFrame}
    {guess : ℕ → Bool} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {reg : Bank w} {mem : Memory w}
    {I : Type*} [Fintype I] {host : I → Fin ar.cells} {key : I ↪ ℕ} {sizes : I → ℕ}
    {d : ℕ} {P A : Type*} {bits : P → ℕ} {N : Network d P bits} {cell : N.Site → Fin ar.cells}
    {recv : A → Fin ar.cells} {amount : A → ℕ}

local notation3 (prettyPrint := false) "Site₀" => CandidateSite (X:=X) ar D pp lp word owner decl group
  frame base pins fields f guess pub mac reg mem host key sizes N cell recv amount

/-- The planner reads the same return at the installed library and at its
calibrated cube layout. The chronological observation retains the original
type of native executions. -/
theorem CandidateSite.at_planner_return {installed : TeamOpcode.Macros w 8}
    (library : mac=installed) (br : CubeArena.Layout) (layout : ar=br)
    {T : Type*} {old : Fin 81 → Word w} {fresh gates outputs width off ell controls : ℕ}
    {profile : List Bool} {claims : List (List Bool)} {pad used : ℕ} {preRegs : T → Bank w} {preMem : T → Memory w}
    {charged : T → ℕ} {physical : T → Prop}
    (received : ∃ (t : T) (s : Site₀), s.OnReturn old fresh gates outputs width off ell controls profile claims
      pad (preRegs t) (preMem t) used (charged t) ∧ physical t) :
    ∃ (t : T) (s : CandidateSite (X:=X) br D pp lp
      (cast (congrArg (fun a : CubeArena.Layout => Broadcast a.n a.header.d a.header.cap) layout) word) owner
      (cast (congrArg (fun a : CubeArena.Layout => LengthDeclaration a.n a.header.d) layout) decl)
      (cast (congrArg (fun a : CubeArena.Layout => Fin a.header.d → Fin (R+1)) layout) group)
      frame base pins fields f guess pub installed reg mem
      (cast (congrArg (fun a : CubeArena.Layout => I → Fin a.cells) layout) host) key sizes N
      (cast (congrArg (fun a : CubeArena.Layout => N.Site → Fin a.cells) layout) cell)
      (cast (congrArg (fun a : CubeArena.Layout => A → Fin a.cells) layout) recv) amount),
      s.OnReturn old fresh gates outputs width off ell controls profile claims
        pad (preRegs t) (preMem t) used (charged t) ∧ physical t := by
  exact CandidateSite.reindex_return br layout (CandidateSite.reindex_library_return library received)

open Lean Meta Elab Term

private def expectHead (type : Expr) (head : Name) : MetaM Expr := do
  let some app ← whnfUntil type head | throwError "expected {head} in the candidate return"
  return app

private def plannerArguments (app : Expr) : MetaM (NameMap Expr) := do
  let info ← getConstInfo app.getAppFn.constName!
  forallTelescope info.type fun binders _ => do
    let mut values : NameMap Expr := {}
    for param in binders, arg in app.getAppArgs do
      let decl ← param.fvarId!.getDecl
      values := values.insert decl.userName arg
      if decl.binderInfo.isInstImplicit then values := values.insert `inventoryInstance arg
    return values

private def plannerArgument (map : NameMap Expr) (name : Name) : MetaM Expr := do
  let some out := map.find? name | throwError "missing planner return parameter {name}"
  return out

/-- Apply the two proved changes of indices using the parameters of the real
site and its return evidence. The term retains the register, RAM and charge
functions of the quantified execution. -/
elab "returnedSiteAtPlanner%" received:term:max library:term:max layout:term:max : term => do
  let received ← elabTerm received none
  let library ← elabTerm library none
  let layout ← elabTerm layout none
  let macEq ← expectHead (← inferType library) ``Eq
  let arEq ← expectHead (← inferType layout) ``Eq
  let outer ← expectHead (← inferType received) ``Exists
  let T := outer.getAppArgs[0]!
  withLocalDeclD `execution T fun t => do
    let inner ← expectHead ((mkApp outer.getAppArgs[1]! t).headBeta) ``Exists
    let siteApp ← expectHead inner.getAppArgs[0]! ``CandidateSite
    withLocalDeclD `site siteApp fun site => do
      let both ← expectHead ((mkApp inner.getAppArgs[1]! site).headBeta) ``And
      let onReturn ← expectHead both.getAppArgs[0]! ``CandidateSite.OnReturn
      let mut values ← plannerArguments siteApp
      let on ← plannerArguments onReturn
      for name in [`old,`fresh,`gates,`outputs,`width,`off,`ell,`controls,`profile,`claims,`pad,`used] do
        values := values.insert name (← plannerArgument on name)
      for name in [`preRegs,`preMem,`charged] do
        values := values.insert name (← mkLambdaFVars #[t] (← plannerArgument on name))
      values := values.insert `physical (← mkLambdaFVars #[t] both.getAppArgs[1]!)
      values := values.insert `base (← plannerArgument values `receivingBase)
        |>.insert `d (← plannerArgument values `D₀)
        |>.insert `T T |>.insert `br arEq.getAppArgs[2]! |>.insert `installed macEq.getAppArgs[2]!
        |>.insert `layout layout |>.insert `library library |>.insert `received received
      let info ← getConstInfo ``CandidateSite.at_planner_return
      forallTelescope info.type fun params _ => do
        let mut levels : NameMap Level := {}
        let mut actuals := #[]
        for param in params do
          let decl ← param.fvarId!.getDecl
          let key := if decl.binderInfo.isInstImplicit then `inventoryInstance else decl.userName
          let value ← plannerArgument values key
          actuals := actuals.push value
          if let .sort (.succ (.param u)) := decl.type then
            levels := levels.insert u (← getDecLevel value)
        let uv ← info.levelParams.mapM fun u => do
          let some v := levels.find? u | throwError "missing universe {u} of the planner return"
          return v
        return mkAppN (Lean.mkConst info.name uv) actuals

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
