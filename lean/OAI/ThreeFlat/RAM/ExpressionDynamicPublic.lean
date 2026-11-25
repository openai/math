import OAI.ThreeFlat.RAM.DescriptorExpr

namespace OAI
/-! # Replacing public parameter reads with expressions over the original operand registers -/

namespace ThreeFlat.RAM.DescriptorExpr

open Computability.VPVNP.BurstRAM PrivateRAM
variable {w k K n : ℕ}

private def publicOp (op : Op w k n) (arg : Fin k→Term w K n) : Term w K n :=
  match op with
  | .literal x => .literal x
  | .parameter i => arg i
  | .binary b x y => .bind (.binary b x y) (.result 0)
  | .load x => .bind (.load x) (.result 0)
  | .select c x y t f => .bind (.select c x y t f) (.result 0)

/-- At each binding, move the original operand registers one slot past the new result. -/
def Term.withPublic : {n : ℕ} → Term w k n → (Fin k→Term w K n) → Term w K n
  | _,.result i,_ => .result i
  | _,.bind op tail,arg => (publicOp op arg).letThen
      (tail.withPublic (fun i => (arg i).rename Fin.succ))

private theorem publicOp_eval (op : Op w k n) (arg : Fin k→Term w K n)
    (data : Fin K→Word w) (mem : Memory w) (vs : Fin n→Word w) :
    (publicOp op arg).eval data mem vs =
      op.eval (fun i => (arg i).eval data mem vs) vs mem := by
  cases op <;> rfl

private theorem upParams (arg : Fin k→Term w K n) (data : Fin K→Word w)
    (mem : Memory w) (vs : Fin n→Word w) (x : Word w) :
    (fun i => ((arg i).rename Fin.succ).eval data mem (Fin.cons x vs)) =
      (fun i => (arg i).eval data mem vs) := by
  funext i
  simp only [Term.eval_rename,Function.comp_def,Fin.cons_succ]

theorem Term.eval_withPublic (e : Term w k n) (arg : Fin k→Term w K n)
    (data : Fin K→Word w) (mem : Memory w) (vs : Fin n→Word w) :
    (e.withPublic arg).eval data mem vs = e.eval (fun i => (arg i).eval data mem vs) mem vs := by
  induction e with
  | result i => rfl
  | bind op tail ih =>
    rw [withPublic,eval_letThen,ih,upParams,publicOp_eval,eval]

private theorem publicOp_binds (op : Op w k n) (arg : Fin k→Term w K n) (M : ℕ)
    (size : ∀ i,(arg i).binds≤M) : (publicOp op arg).binds≤max 1 M := by
  cases op with
  | parameter i => exact (size i).trans (Nat.le_max_right _ _)
  | literal | binary | load | select => exact Nat.le_max_left _ _

theorem Term.binds_withPublic (e : Term w k n) (arg : Fin k→Term w K n) (M : ℕ)
    (size : ∀ i,(arg i).binds≤M) : (e.withPublic arg).binds ≤ e.binds * max 1 M := by
  induction e with
  | result i => simp [withPublic,binds]
  | bind op tail ih =>
    have shifted (i : Fin k) : ((arg i).rename Fin.succ).binds≤M := by simpa using size i
    have bs := ih (fun i => (arg i).rename Fin.succ) shifted
    have a := publicOp_binds op arg M size
    simp only [withPublic,binds_letThen,binds,Nat.add_mul,Nat.one_mul]
    omega

end ThreeFlat.RAM.DescriptorExpr

end OAI
