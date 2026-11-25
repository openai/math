import OAI.Computability.NearSquareRoot.InterchangeROMStageTableMatrix

/-! # Primitive recursive construction of the physical rectangle matrices -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStageTable
open InterchangeROMStage

section
variable {X A C : Type} [Primcodable X] [Primcodable A] [Primcodable C]

private theorem prEq {a b : X → A} [DecidableEq A] {yes no : X → C}
    (ha : Primrec a) (hb : Primrec b) (hy : Primrec yes) (hn : Primrec no) :
    Primrec fun x => if a x = b x then yes x else no x :=
  Primrec.ite (Primrec.eq.comp ha hb) hy hn

private theorem prGet {a : X → List A} {i : X → ℕ} (d : A)
    (ha : Primrec a) (hi : Primrec i) : Primrec fun x => ((a x)[i x]?).getD d :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp ha hi) (Primrec.const d)

private theorem prAcross {n : X → ℕ} {f : X → ℕ → List Term} (hn : Primrec n)
    (hf : Primrec fun z : X × ℕ => f z.1 z.2) :
    Primrec fun x => across (n x) (f x) :=
  Primrec.list_flatMap (Primrec.list_range.comp hn) hf.to₂

private theorem prFst {u : X → A × C} (h : Primrec u) : Primrec fun x => (u x).1 :=
  Primrec.fst.comp h
private theorem prSnd {u : X → A × C} (h : Primrec u) : Primrec fun x => (u x).2 :=
  Primrec.snd.comp h

private theorem prAdd {a b : X → ℕ} (ha : Primrec a) (hb : Primrec b) : Primrec fun x => a x + b x :=
  Primrec.nat_add.comp ha hb
private theorem prMul {a b : X → ℕ} (ha : Primrec a) (hb : Primrec b) : Primrec fun x => a x * b x :=
  Primrec.nat_mul.comp ha hb
private theorem prSub {a b : X → ℕ} (ha : Primrec a) (hb : Primrec b) : Primrec fun x => a x - b x :=
  Primrec.nat_sub.comp ha hb
private theorem prCons {a : X → A} {b : X → List A} (ha : Primrec a) (hb : Primrec b) :
    Primrec fun x => a x :: b x := Primrec.list_cons.comp ha hb
private theorem prAppend {a b : X → List A} (ha : Primrec a) (hb : Primrec b) :
    Primrec fun x => a x ++ b x := Primrec.list_append.comp ha hb
private theorem prLength {a : X → List A} (h : Primrec a) :
    Primrec fun x => (a x).length := Primrec.list_length.comp h
private theorem prPair {a : X → A} {b : X → C} (ha : Primrec a) (hb : Primrec b) :
    Primrec fun x => (a x,b x) := ha.pair hb

/- Prove primitive recursion by following the expression tree of this first-order
finite list program. Expressions below bind only the input and list indices. -/
open Lean Elab Tactic Meta in
local elab "stage_pr_step" : tactic => do
  let target ← getMainTarget
  let f := target.getAppArgs.back!
  let kind ← forallBoundedTelescope (← inferType f) (some 1) fun args _ => do
    let body := (← instantiateMVars (mkAppN f args)).headBeta
    if !(args.any fun a => body.containsFVar a.fvarId!) then return `constant
    if args.contains body then return `identity
    let name := body.getAppFn.constName?
    if let .proj _ i _ := body then return if i == 0 then ``prFst else ``prSnd
    match name with
    | some ``Prod.fst => return ``prFst
    | some ``Prod.snd => return ``prSnd
    | some ``Prod.mk => return ``prPair
    | some ``List.cons => return ``prCons
    | some ``HAppend.hAppend => return ``prAppend
    | some ``List.length => return ``prLength
    | some ``Option.getD => return ``prGet
    | some ``HAdd.hAdd => return ``prAdd
    | some ``HMul.hMul => return ``prMul
    | some ``HSub.hSub => return ``prSub
    | some ``ite => return ``prEq
    | some ``across => return ``prAcross
    | _ => throwError "unknown stage operation {body} ({name})"
  if kind == `constant then evalTactic (← `(tactic| exact Primrec.const _))
  else if kind == `identity then evalTactic (← `(tactic| exact Primrec.id))
  else if kind == ``prGet then evalTactic (← `(tactic| apply prGet _))
  else evalTactic (← `(tactic| apply $(mkIdent kind)))

set_option maxHeartbeats 700000

local macro "stage_pr" : tactic => `(tactic| repeat' stage_pr_step)

private theorem primrec_partials : Primrec (fun z : Parameters × Ground =>
    partials (decode z.1) z.2.1 z.2.2) := by
  simp only [partials,decode,Frame.labels,Frame.incident,Frame.mask,Frame.boxes,Bool.toNat_false,
    Nat.zero_mul,Nat.zero_add,active,term]
  stage_pr

private theorem primrec_mix : Primrec (fun z : Parameters × Ground =>
    mix (decode z.1) z.2.1 z.2.2) := by
  simp only [mix,decode,Frame.minor,Frame.incident,Frame.mask,Frame.boxes,Frame.labels,Bool.toNat_true,
    Nat.one_mul,ite_true,read,rankTerm,term]
  stage_pr

private theorem primrec_scatter : Primrec (fun z : Parameters × Ground =>
    scatter (decode z.1) z.2.1 z.2.2) := by
  simp only [scatter,decode,Frame.minor,Frame.incident,Frame.mask,Frame.boxes,Frame.labels,
    Bool.toNat_false,Nat.zero_mul,Nat.zero_add,ite_true,Bool.false_eq_true,ite_false,rect,rankTerm,term]
  stage_pr

private theorem primrec_collect : Primrec (fun z : Parameters × Ground =>
    collect (decode z.1) z.2.1 z.2.2) := by
  simp only [collect,decode,Frame.queries,read,active,label,plain,term]
  stage_pr

private theorem primrec_finish : Primrec (fun z : Parameters × Ground =>
    finish (decode z.1) z.2.1 z.2.2) := by
  simp only [finish,decode,Frame.incident,Frame.mask,Frame.boxes,Frame.labels,Bool.toNat_true,
    Nat.one_mul,reserve,term]
  stage_pr

theorem primrec_terms : Primrec (fun z : Parameters × ℕ × Ground => terms (decode z.1) z.2.1 z.2.2) := by
  let u := fun z : Parameters × ℕ × Ground => (z.1,z.2.2)
  have hu : Primrec u := Primrec.fst.pair (Primrec.snd.comp Primrec.snd)
  have hk : Primrec fun z : Parameters × ℕ × Ground => z.2.1 := Primrec.fst.comp Primrec.snd
  apply (prEq hk (Primrec.const 0) (primrec_partials.comp hu)
    (prEq hk (Primrec.const 1) (primrec_mix.comp hu)
      (prEq hk (Primrec.const 2) (primrec_scatter.comp hu)
        (prEq hk (Primrec.const 3) (primrec_collect.comp hu) (primrec_finish.comp hu))))).of_eq
  rintro ⟨c,n,o⟩
  rcases n with _ | (_ | (_ | (_ | n))) <;> rfl

private theorem prSum : Primrec (List.sum : List ℕ → ℕ) := by
  apply (Primrec.list_foldr (Primrec.id (α:=List ℕ)) (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (x+·) ih

theorem primrec_coefficient : Primrec (fun z : List Term × Ground => coefficient z.1 z.2) := by
  apply prSum.comp
  apply Primrec.list_map Primrec.fst
  change Primrec (fun z : (List Term × Ground) × Term => if z.2.1 = z.1.2 then z.2.2 else 0)
  stage_pr

theorem primrec_expandRoles : Primrec₂ expandRoles := by
  apply Primrec.list_flatMap Primrec.fst
  change Primrec (fun z : (List Role × ℕ) × Role => (List.range z.1.2).map fun k => (z.2,k))
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.snd.comp Primrec.fst))
  exact ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂

end
end InterchangeROMStageTable

end NearSquareRoot
end Computability
end OAI
