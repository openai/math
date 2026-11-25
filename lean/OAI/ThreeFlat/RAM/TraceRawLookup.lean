import OAI.ThreeFlat.RAM.ExpressionDynamicPublic
import OAI.ThreeFlat.RAM.FixedTraceProgram
import OAI.ThreeFlat.RAM.TraceRawOverlay

namespace OAI
/-! # Computing selected H-trace source records directly from the physical template -/

namespace ThreeFlat.RAM.TraceRawLookup
open Computability.VPVNP.BurstRAM DescriptorExpr
open scoped Fin.CommRing

structure Layout where
  raw : ℕ
  rows : ℕ
  publicBase : ℕ

variable {W n k : ℕ}

private def backed (base : ℕ) (e : Term W FixedTraceProgram.P n) : Term W k n :=
  e.withPublic (fun j=>Term.load (.literal (base+j.val : ℕ)))

/-- Public arguments of the fixed trace generator are eighteen read-only words. -/
def words (R : Layout) (m : Memory W) : Fin FixedTraceProgram.P→Word W :=fun j=>m (R.publicBase+j.val)

private theorem eval_backed (R : Layout) (data : Fin k→Word W) (m : Memory W)
    (fit : R.publicBase+FixedTraceProgram.P≤2^W) (e : Term W FixedTraceProgram.P n) (v : Fin n→Word W) :
    (backed R.publicBase e).eval data m v=e.eval (words R m) m v := by
  have fitAt (i : Fin FixedTraceProgram.P) : R.publicBase+i.val<2^W:=
    (Nat.add_lt_add_left i.isLt _).trans_le fit
  simp only [backed,Term.eval_withPublic,Term.eval_load,Term.eval_literal,
    Fin.val_cast_of_lt (fitAt _)]
  rfl

private theorem backed_size (base : ℕ) (e : Term W FixedTraceProgram.P n) :
    (backed (k:=k) base e).binds≤2*e.binds := by
  dsimp only [backed]
  simpa only [show max 1 2=2 by decide,Nat.mul_comm] using
    (Term.binds_withPublic e (fun j=>(Term.load (.literal (base+j.val:ℕ)) : Term W k n)) 2
      (fun _=>le_rfl))

/-- Only the assigned raw window is interpreted as trace-record addresses. All
dictionary, endpoint, sparse table, and ordinary register loads still read RAM. -/
def access (W : ℕ) (R : Layout) (i : Fin n) : Term W k n :=
  let address : Term W k n:=.result i
  let plain:=Term.load address
  let row:=(backed R.publicBase (FixedTraceProgram.program W)).rename (fun _=>i)
  .select .lt address (.literal R.raw) plain
    (.select .lt address (.literal (R.raw+11*R.rows:ℕ)) row plain)

def virtual (W : ℕ) (R : Layout) : {n : ℕ} → Term W k n → Term W k n
  | _,.result i=>.result i
  | _,.bind op body=>
    match op with
    | .load i=>(access W R i).letThen (virtual W R body)
    | _=>.bind op (virtual W R body)

theorem access_binds (R : Layout) (i : Fin n) : (access (k:=k) W R i).binds≤866 := by
  have hb:=backed_size (W:=W) (k:=k) R.publicBase (FixedTraceProgram.program W)
  have hf:=FixedTraceProgram.size W
  simp only [access,Term.select,Term.load,Term.literal,Term.binds_letThen,Term.binds_rename,Term.binds]
  omega

theorem virtual_binds (W : ℕ) (R : Layout) (e : Term W k n) :
    (virtual W R e).binds≤866*e.binds := by
  induction e with
  | result _=>simp [virtual,Term.binds]
  | bind op b ih=>
    cases op with
    | load i=>
      simp only [virtual,Term.binds_letThen,Term.binds]
      have twice:=access_binds (W:=W) (k:=k) R i
      omega
    | _=>simp only [virtual,Term.binds]; omega

variable {F : Type*} {p : ℕ}
variable (N : BitNetwork F p) (code : FieldCode F W) (R : Layout) (m : Memory W)

/-- The single concrete scalar equation supplied by the packed H gate/port
prototype and its row-dependent trace addressing records. -/
def Sources : Prop :=
  ∀ a : Word W,R.raw≤a.val → a.val<R.raw+11*R.rows →
    (FixedTraceProgram.program W).eval (words R m) m (fun _=>a)=TraceRawOverlay.memory N code R.raw m a.val

theorem access_eval (data : Fin k→Word W) (v : Fin n→Word W) (i : Fin n)
    (rows : R.rows=N.cells) (endFit : R.raw+11*R.rows<2^W)
    (headFit : R.publicBase+FixedTraceProgram.P≤2^W) (source : Sources N code R m) :
    (access W R i).eval data m v=TraceRawOverlay.memory N code R.raw m (v i).val := by
  have startFit : R.raw<2^W:=by omega
  simp only [access,Term.eval_select,Term.eval_literal,Term.eval_load,Term.eval_rename,Term.eval,
    Comparison.test,Fin.lt_def,decide_eq_true_eq,Fin.val_cast_of_lt startFit,Fin.val_cast_of_lt endFit]
  by_cases before : (v i).val<R.raw
  · rw [ite_eq_left before]
    exact (TraceRawOverlay.outside N code R.raw m (.inl before)).symm
  · rw [ite_eq_right before]
    by_cases hi : (v i).val<R.raw+11*R.rows
    · rw [ite_eq_left hi,eval_backed R data m headFit]
      exact source _ (Nat.le_of_not_gt before) hi
    · rw [ite_eq_right hi]
      exact (TraceRawOverlay.outside N code R.raw m (.inr (by omega))).symm

theorem eval_virtual (e : Term W k n) (data : Fin k→Word W) (v : Fin n→Word W)
    (rows : R.rows=N.cells) (endFit : R.raw+11*R.rows<2^W)
    (headFit : R.publicBase+FixedTraceProgram.P≤2^W) (source : Sources N code R m) :
    (virtual W R e).eval data m v=e.eval data (TraceRawOverlay.memory N code R.raw m) v := by
  induction e with
  | result i=>rfl
  | bind op b ih=>
    cases op with
    | load i=>
      simp only [virtual,Term.eval_letThen,Term.eval,Op.eval,ih,
        access_eval N code R m data v i rows endFit headFit source]
    | _=>simp only [virtual,Term.eval,Op.eval,ih]

end ThreeFlat.RAM.TraceRawLookup

end OAI
