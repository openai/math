import OAI.ThreeFlat.RAM.ExpressionReads

namespace OAI
/-! # Exact load trace when instantiating an arbitrary number of native operands -/

namespace ThreeFlat.RAM.DescriptorExpr

open Computability.VPVNP.BurstRAM PrivateRAM
open private bindInputs extendEnv extendEnv_skip extendEnv_front from OAI.ThreeFlat.RAM.DescriptorExpr

variable {w k m n : ℕ}

/-- Native argument binding traverses its operand vector from the last variable
to the first, before running the body in the resulting register environment. -/
private theorem reads_bindInputs (args : Fin n → Term w k m) (body : Term w k (m+n))
    (par : Fin k → Word w) (mem : Memory w) (vars : Fin m → Word w) :
    (bindInputs args body).reads par mem vars =
      ((List.ofFn fun i => (args i).reads par mem vars).reverse.flatten ++
        body.reads par mem (extendEnv (fun i => (args i).eval par mem vars) vars)) := by
  induction n with
  | zero => simp [bindInputs,extendEnv]
  | succ n ih =>
    rw [bindInputs,ih,Term.reads_letThen,Term.reads_rename,Term.eval_rename,extendEnv_skip]
    simp [List.ofFn_succ,extendEnv,Function.comp_def,List.append_assoc]

theorem Term.reads_instantiate (expr : Term w k n) (args : Fin n → Term w k m)
    (par : Fin k → Word w) (mem : Memory w) (vars : Fin m → Word w) :
    (expr.instantiate args).reads par mem vars =
      (List.ofFn fun i => (args i).reads par mem vars).reverse.flatten ++
        expr.reads par mem (fun i => (args i).eval par mem vars) := by
  rw [Term.instantiate,reads_bindInputs,Term.reads_rename,extendEnv_front]

theorem Term.readCount_instantiate (expr : Term w k n) (args : Fin n → Term w k m)
    (par : Fin k → Word w) (mem : Memory w) (vars : Fin m → Word w) :
    ((expr.instantiate args).reads par mem vars).length =
      (∑ i, ((args i).reads par mem vars).length) +
      (expr.reads par mem (fun i => (args i).eval par mem vars)).length := by
  rw [reads_instantiate,List.length_append,List.length_flatten,List.map_reverse,List.sum_reverse_nat,List.map_ofFn]
  simp only [Fin.sum_ofFn,Function.comp_apply]

end ThreeFlat.RAM.DescriptorExpr

end OAI
