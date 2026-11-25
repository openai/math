import OAI.ThreeFlat.RAM.DescriptorExpr
import Mathlib.Tactic.FinCases

namespace OAI
/-! # External reads of a descriptor expression -/

namespace ThreeFlat.RAM.DescriptorExpr

open Computability.VPVNP.BurstRAM PrivateRAM

variable {w k n : ℕ}

/-- The addresses read by one primitive operation in the supplied register state. -/
def Op.reads (op : Op w k n) (vs : Fin n → Word w) : List ℕ :=
  match op with
  | .load i => [(vs i).val]
  | _ => []

theorem Op.eval_eq_of_agrees_reads (op : Op w k n) (params : Fin k → Word w)
    (input scratch : Memory w) (vs : Fin n → Word w)
    (agree : ∀ a ∈ op.reads vs, scratch a = input a) :
    op.eval params vs scratch = op.eval params vs input := by
  cases op with
  | load addr => exact agree (vs addr).val (by simp [Op.reads])
  | _ => rfl

/-- External addresses in evaluation order, including repeated probes. Each
bound value is computed in the given input memory before tracing the body. -/
def Term.reads (params : Fin k → Word w) (input : Memory w) :
    {n : ℕ} → Term w k n → (Fin n → Word w) → List ℕ
  | _, .result _, _ => []
  | _, .bind op body, vs =>
    op.reads vs ++ body.reads params input (Fin.cons (op.eval params vs input) vs)

/-- Agreement at the addresses probed by the original evaluation suffices
even when later addresses depend on values loaded by earlier operations. -/
theorem Term.eval_eq_of_agrees_reads (e : Term w k n) (params : Fin k → Word w)
    (input scratch : Memory w) (vs : Fin n → Word w)
    (agree : ∀ a ∈ e.reads params input vs, scratch a = input a) :
    e.eval params scratch vs = e.eval params input vs := by
  induction e with
  | result i => rfl
  | bind op body ih =>
    change ∀ a ∈ op.reads vs ++ _, scratch a = input a at agree
    have equal := op.eval_eq_of_agrees_reads params input scratch vs fun a ha =>
      agree a (List.mem_append_left _ ha)
    simp only [eval, equal]
    exact ih _ fun a ha => agree a (List.mem_append_right _ ha)

@[simp] theorem Op.reads_rename {m : ℕ} (f : Fin n → Fin m) (op : Op w k n)
    (vs : Fin m → Word w) : (op.rename f).reads vs = op.reads (vs ∘ f) := by
  cases op <;> rfl

@[simp] theorem Term.reads_rename {m : ℕ} (e : Term w k n) (f : Fin n → Fin m)
    (params : Fin k → Word w) (input : Memory w) (vs : Fin m → Word w) :
    (e.rename f).reads params input vs = e.reads params input (vs ∘ f) := by
  induction e generalizing m with
  | result _ => rfl
  | bind op body ih =>
    simp only [rename, reads, ih, Op.eval_rename, Op.reads_rename]
    congr 1
    apply congrArg (body.reads params input)
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i <;> simp

@[simp] theorem Term.reads_letThen (e : Term w k n) (cont : Term w k (n+1))
    (params : Fin k → Word w) (input : Memory w) (vs : Fin n → Word w) :
    (e.letThen cont).reads params input vs = e.reads params input vs ++
      cont.reads params input (Fin.cons (e.eval params input vs) vs) := by
  induction e with
  | result i =>
    rw [letThen, reads_rename]
    change cont.reads _ _ _ = cont.reads _ _ _
    apply congrArg (cont.reads params input)
    funext j
    refine Fin.cases ?_ (fun _ => ?_) j <;> simp [eval]
  | bind op b ih =>
    simp only [letThen, reads, eval, ih, reads_rename, List.append_assoc]
    have heq {m : ℕ} (a b : Word w) (xs : Fin m → Word w) :
        Fin.cons a (Fin.cons b xs) ∘ Fin.cons 0 (fun i => i.succ.succ) = Fin.cons a xs := by
      funext i
      refine Fin.cases ?_ (fun _ => ?_) i <;> simp
    rw [heq]

@[simp] theorem Term.reads_literal (v : Word w) (params : Fin k → Word w)
    (input : Memory w) (vs : Fin n → Word w) : (literal v).reads params input vs = [] := rfl

@[simp] theorem Term.reads_parameter (i : Fin k) (params : Fin k → Word w)
    (input : Memory w) (vs : Fin n → Word w) : (parameter i).reads params input vs = [] := rfl

@[simp] theorem Term.reads_load (a : Term w k n) (params : Fin k → Word w)
    (input : Memory w) (vs : Fin n → Word w) : a.load.reads params input vs =
      a.reads params input vs ++ [(a.eval params input vs).val] := by
  simp [load, reads, Op.reads]

@[simp] theorem Term.reads_binary (op : BinaryOp) (a b : Term w k n)
    (params : Fin k → Word w) (input : Memory w) (vs : Fin n → Word w) :
    (binary op a b).reads params input vs = a.reads params input vs ++ b.reads params input vs := by
  simp [binary, reads, Op.reads, Function.comp_def]

/-- The native selection primitive evaluates both candidate words before
the register selection, so both candidate read lists occur in its trace. -/
@[simp] theorem Term.reads_select (cmp : Comparison) (a b yes no : Term w k n)
    (params : Fin k → Word w) (input : Memory w) (vs : Fin n → Word w) :
    (select cmp a b yes no).reads params input vs = a.reads params input vs ++
      (b.reads params input vs ++ (yes.reads params input vs ++ no.reads params input vs)) := by
  simp [select, reads, Op.reads, Function.comp_def]

/-- One-argument stencils evaluate their supplied index first, then perform
the loads in their body with that index in the sole input register. -/
@[simp] theorem Term.reads_instantiate_one (e : Term w k 1) (arg : Term w k n)
    (params : Fin k → Word w) (input : Memory w) (vs : Fin n → Word w) :
    (e.instantiate (fun _ => arg)).reads params input vs = arg.reads params input vs ++
      e.reads params input (fun _ => arg.eval params input vs) := by
  let front (i : Fin 1) : Fin (n+1) := ⟨i.val, by omega⟩
  change ((arg.rename id).letThen (e.rename front)).reads params input vs = _
  simp only [reads_letThen, reads_rename, eval_rename, Function.comp_id]
  congr 1
  apply congrArg (e.reads params input)
  funext i
  have hz : i = 0 := Subsingleton.elim _ _
  subst i
  have front_zero : front 0 = 0 := Fin.ext rfl
  simp [front_zero]

/-- For two-input stencils the native binder evaluates the second argument
before the first. The first argument is then at variable zero. -/
@[simp] theorem Term.reads_instantiate_two (e : Term w k 2) (args : Fin 2 → Term w k n)
    (params : Fin k → Word w) (input : Memory w) (vs : Fin n → Word w) :
    (e.instantiate args).reads params input vs = (args 1).reads params input vs ++
      ((args 0).reads params input vs ++ e.reads params input (fun i => (args i).eval params input vs)) := by
  let front (i : Fin 2) : Fin ((n+1)+1) := ⟨i.val, by omega⟩
  change (((args 1).rename id).letThen (((args 0).rename Fin.succ).letThen
    (e.rename front))).reads params input vs = _
  simp only [reads_letThen, reads_rename, eval_rename, Function.comp_def, Fin.cons_succ]
  congr 1
  congr 1
  apply congrArg (e.reads params input)
  funext i
  have f0 : front 0 = 0 := Fin.ext rfl
  have f1 : front 1 = (0 : Fin (n+1)).succ := Fin.ext rfl
  fin_cases i <;> simp [f0, f1]

end ThreeFlat.RAM.DescriptorExpr

end OAI
