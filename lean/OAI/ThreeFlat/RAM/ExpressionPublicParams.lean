import OAI.ThreeFlat.RAM.ExpressionReads

namespace OAI
/-! # Relabeling public word operands of a native descriptor expression -/

namespace ThreeFlat.RAM.DescriptorExpr

open Computability.VPVNP.BurstRAM PrivateRAM
variable {w k l n : ℕ}

def Op.reparam (f : Fin k → Fin l) : Op w k n → Op w l n
  | .literal x => .literal x
  | .parameter i => .parameter (f i)
  | .binary op a b => .binary op a b
  | .load addr => .load addr
  | .select cmp a b yes no => .select cmp a b yes no

@[simp] theorem Op.eval_reparam (op : Op w k n) (f : Fin k → Fin l) (data : Fin l → Word w)
    (vs : Fin n → Word w) (mem : Memory w) : (op.reparam f).eval data vs mem = op.eval (data ∘ f) vs mem := by
  cases op <;> rfl

@[simp] theorem Op.reads_reparam (op : Op w k n) (f : Fin k → Fin l) (vs : Fin n → Word w) :
    (op.reparam f).reads vs = op.reads vs := by cases op <;> rfl

/-- Supply a stencil compiled for one public-data ABI to a surrounding machine
that stores the same operands at other public register indices. -/
def Term.reparam (f : Fin k → Fin l) : {n : ℕ} → Term w k n → Term w l n
  | _, .result i => .result i
  | _, .bind op b => .bind (op.reparam f) (b.reparam f)

@[simp] theorem Term.eval_reparam (e : Term w k n) (f : Fin k → Fin l) (data : Fin l → Word w)
    (mem : Memory w) (vs : Fin n → Word w) : (e.reparam f).eval data mem vs = e.eval (data ∘ f) mem vs := by
  induction e with
  | result => rfl
  | bind op b ih => simp only [reparam,eval,ih,Op.eval_reparam]

@[simp] theorem Term.reads_reparam (e : Term w k n) (f : Fin k → Fin l) (data : Fin l → Word w)
    (mem : Memory w) (vs : Fin n → Word w) : (e.reparam f).reads data mem vs = e.reads (data ∘ f) mem vs := by
  induction e with
  | result => rfl
  | bind op b ih => simp only [reparam,reads,ih,Op.reads_reparam,Op.eval_reparam]

@[simp] theorem Term.binds_reparam (e : Term w k n) (f : Fin k → Fin l) : (e.reparam f).binds = e.binds := by
  induction e with
  | result => rfl
  | bind op b ih => simp only [reparam,binds,ih]

/-- A public stencil can follow an arbitrary block of driver-owned public words. -/
theorem params_afterPrefix (front : Fin l → Word w) (data : Fin k → Word w) :
    (Fin.addCases front data) ∘ Fin.natAdd l = data := by funext i; simp

end ThreeFlat.RAM.DescriptorExpr

end OAI
