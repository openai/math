import OAI.Computability.NearSquareRoot.CommonRegisters
import OAI.Computability.IntegerMultiplication.Code.Product
import Lean

/-! # Register bounds for concrete command witnesses

The P192 `Task` and the bounded-space variant both assert the existence of a
command. The proof elaborator below replays existential introductions and
eliminations from their proofs, retaining the actual instruction tree. Lean
checks the register bounds at every introduced command, including all the
branches of each inspection.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RegisterWitness
open IntegerMultiplication Code CommonRegisters

/-- A concrete register restriction on the same command that performs the task. -/
def Checked (R : ℕ) (P : Cmd → Prop) := ∃ c, Within R c ∧ P c

/-- The original P192 time, input, and output contract at the restricted command. -/
abbrev Timed {X : Type*} (R : ℕ) (a : X → ℕ) (p q : X → Tree) :=
  Checked R fun c => ∃ C, ∀ x env, Fits.value env c 0 (p x) (q x) (C*(a x+1))

/-- A register-bounded instance of the P192 linear-time interface. -/
abbrev Easy {X Y : Type*} [Codec X] [Codec Y] (R : ℕ) (f : X → Y) :=
  Timed R size send (fun x => send (f x))

/-- The bounded-space interface on the same restricted command. -/
abbrev Bounded {X : Type*} (R : ℕ) (T S : X → ℕ) (p q : X → Tree) :=
  Checked R fun c => ∃ C, ∀ x env r base, (∀ j, (letters r j).length ≤ base) →
    Space.BoundedFits env c (pile 0 (p x) r) (pile 0 (q x) r)
      (C*(T x+1)) (base+C*(S x+1)) (C*(S x+1))

theorem forget {R : ℕ} {P : Cmd → Prop} (h : Checked R P) : ∃ c, P c := by
  obtain ⟨c,_,hc⟩ := h
  exact ⟨c,hc⟩

theorem combine {R : ℕ} {P : Cmd → Prop} {Q : Prop} (h : Checked R P)
    (f : ∀ c, Within R c → P c → Q) : Q := by
  obtain ⟨c,hR,hc⟩ := h
  exact f c hR hc

@[simp] theorem splitRoot_within {R i} {f : Bool → Cmd} {p : Cmd} :
    Within R (splitRoot i f p) ↔ i < R ∧ Within R (f false) ∧ Within R (f true) ∧ Within R p := by
  simp only [splitRoot, Within]
  constructor
  · rintro ⟨hi,h⟩
    exact ⟨hi,(h (some (.bit false))).2,(h (some (.bit true))).2,(h (some .node)).2⟩
  · rintro ⟨hi,hf,ht,hp⟩
    refine ⟨hi, fun a => ⟨hi, ?_⟩⟩
    rcases a with _|(_|_|_) <;> try trivial
    next b => cases b <;> assumption

@[simp] theorem prepare_within {R i} (x : Tree) :
    Within R (Task.prepare i x) ↔ i < R := by
  induction x with
  | atom => rfl
  | fork x y hx hy => simp [Task.prepare, Within, hx, hy, pack]

open Lean Meta Elab Term

private def expandProof (h : Expr) : TermElabM Expr := do
  let f := h.getAppFn
  let args := h.getAppArgs
  match f with
  | .const name levels =>
    let info ← getConstInfo name
    let some body := info.value? true | throwError "no proof body for {name}"
    return (body.instantiateLevelParams info.levelParams levels).betaRev args.reverse true
  | .letE _ _ val body _ => return (body.instantiate1 val).betaRev args.reverse true
  | .lam .. => return f.betaRev args.reverse true
  | .fvar id =>
    let some value := (← id.getDecl).value? | throwError "register bound needed for {h}"
    return value.betaRev args.reverse true
  | .mdata _ body => return mkAppN body args
  | _ => throwError "unsupported witness expression {f}"

/-- Strengthen a task-valued predicate pointwise, including partially applied predicates
inside the congruence proof of a rewrite. -/
private def liftPredicate (lift : Expr → MetaM Expr) (f : Expr) : MetaM Expr := do
  forallTelescopeReducing (← inferType f) fun xs _ => do
    let proposition ← whnf (f.beta xs)
    unless proposition.isAppOfArity ``Exists 2 do
      throwError "expected a command witness in {proposition}"
    mkLambdaFVars xs (← lift proposition.appArg!)

private def restrictPredicate (R : Expr) := liftPredicate (fun p => mkAppM ``Checked #[R,p])

/-- Rewrite the same task indices after adding the command restriction. -/
private partial def mapCongr (lift : Expr → MetaM Expr) (eqn : Expr) : TermElabM Expr := do
  withIncRecDepth do
    let e := eqn.consumeMData
    let a := e.getAppArgs
    match e.getAppFn.constName? with
    | some ``congr => mkAppM ``congr #[← mapCongr lift a[6]!,a[7]!]
    | some ``congrArg => mkAppM ``congrArg #[← liftPredicate lift a[4]!,a[5]!]
    | some ``congrFun | some ``congrFun' => mkAppM ``congrFun #[← mapCongr lift a[4]!,a[5]!]
    | some ``Eq.trans => mkAppM ``Eq.trans #[← mapCongr lift a[4]!,← mapCongr lift a[5]!]
    | some ``Eq.symm => mkAppM ``Eq.symm #[← mapCongr lift a.back!]
    | some ``Eq.refl => mkEqRefl (← liftPredicate lift a.back!)
    | some ``id => mapCongr lift a.back!
    | _ => throwError "unsupported congruence in command witness: {e.getAppFn}"

private partial def replay (R h : Expr) : TermElabM Expr := do
  withIncRecDepth do
    let h := h.consumeMData
    -- A previously checked leaf may package a long arithmetic proof or an
    -- independently verified finite table. Match its complete specification.
    let target ← restrictPredicate R (← inferType h)
    for decl in ← getLCtx do
      if !decl.isImplementationDetail && (← isDefEq decl.type target) then
        return decl.toExpr
    let args := h.getAppArgs
    let name := h.getAppFn.constName?
    if name == some ``forget then return args.back!
    if name == some ``Eq.mp || name == some ``Eq.mpr then
      let eqn ← mapCongr (fun p => mkAppM ``Checked #[R,p]) args[2]!
      return ← mkAppM name.get! #[eqn, ← replay R args[3]!]
    if name == some ``Exists.intro then
      let c := args[2]!
      let P := args[1]!
      let goal ← mkAppM ``Within #[R,c]
      let bound ← elabTermEnsuringType (← `(by
        solve
        | assumption
        | simp [Within, Code.move, Code.clone, Code.discard, Code.forward, Code.forwardBody,
            Code.flood, Code.pack, Code.give, *] <;> omega )) goal
      let checked ← mkAppM ``And.intro #[bound,args[3]!]
      let pred ← withLocalDeclD `c (← inferType c) fun v => do
        mkLambdaFVars #[v] (← mkAppM ``And #[← mkAppM ``Within #[R,v], P.beta #[v]])
      return mkAppN (mkConst ``Exists.intro [Level.one]) #[← inferType c,pred,c,checked]
    if name == some ``Exists.casesOn || name == some ``Exists.elim || name == some ``Exists.rec then
      let (src,cont) := if name == some ``Exists.rec then (args[4]!,args[3]!)
        else (args[3]!,args[4]!)
      let T := args[0]!
      let P := args[1]!
      let cmd ← isDefEq T (mkConst ``Cmd)
      let src' ← if cmd then replay R src else pure src
      let body ← withLocalDeclD `w T fun w =>
        withLocalDeclD `hw (P.beta #[w]) fun hw => do
          let rest := cont.beta #[w,hw]
          if cmd then
            withLocalDeclD `within (← mkAppM ``Within #[R,w]) fun hR => do
              mkLambdaFVars #[w,hR,hw] (← replay R rest)
          else mkLambdaFVars #[w,hw] (← replay R rest)
      return ← mkAppM (if cmd then ``combine else ``Exists.elim) #[src',body]
    replay R (← expandProof h)

/-- Replay a `Task` or `BoundedTask` proof, retaining its register bound. -/
elab "register_witness " R:term:max " from " h:term : term => do
  let r ← elabTermEnsuringType R (mkConst ``Nat)
  let pr ← elabTerm h none
  synthesizeSyntheticMVarsNoPostponing
  replay r (← instantiateMVars pr)

/-- Select the actual command and the evidence returned for that command. A
resource majorant may be chosen in a proof; it does not become part of an
explicitly specified executable command. -/
private partial def extract (e : Expr) : TermElabM (Expr × Expr) := do
  withIncRecDepth do
    let h := e.consumeMData
    let args := h.getAppArgs
    let name := h.getAppFn.constName?
    if name == some ``Exists.intro then return (args[2]!,args[3]!)
    if name == some ``Eq.mp || name == some ``Eq.mpr then
      let (c,p) ← extract args[3]!
      let he ← mapCongr (fun pred => pure (pred.beta #[c])) args[2]!
      return (c,← mkAppM name.get! #[he,p])
    if name == some ``Exists.casesOn || name == some ``Exists.elim || name == some ``Exists.rec then
      let (src,cont) := if name == some ``Exists.rec then (args[4]!,args[3]!) else (args[3]!,args[4]!)
      let (w,hw) ← if ← isDefEq args[0]! (mkConst ``Cmd) then extract src else
        pure (← mkAppM ``Classical.choose #[src],← mkAppM ``Classical.choose_spec #[src])
      extract (cont.beta #[w,hw])
    else extract (← expandProof h)

/-- Recover the run contract for a caller-specified command. The kernel checks
that the command appearing in the original P192 proof is definitionally equal
to the specified command. -/
elab "command_contract " c:term:max " from " h:term : term => do
  let cmd ← elabTermEnsuringType c (mkConst ``Cmd)
  let proof ← elabTerm h none
  synthesizeSyntheticMVarsNoPostponing
  let (actual,contract) ← extract (← instantiateMVars proof)
  unless ← isDefEq cmd actual do
    throwError "specified command {cmd} differs from the P192 witness {actual}"
  pure contract

end RegisterWitness

end NearSquareRoot
end Computability
end OAI
