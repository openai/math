import OAI.Computability.BorderVNP.CellBooleanBytecode
import OAI.Computability.BorderVNP.CellSparseSemantics

/-! # Compiling sparse equality ranges and zero pins into private instructions -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro

/-- Symbolic bit address of a copy and lane inside a bounded generator loop. -/
def Port.expr (p : Port) (i k : NatExpr) : NatExpr :=
  .add (.add (.lit p.base) (.mul i (.lit p.copyStride))) (.mul k (.lit p.laneStride))

@[simp] theorem Port.eval_expr (p : Port) (i k : NatExpr) (e : List ℕ) :
    (p.expr i k).eval e = p.atBit (i.eval e) (k.eval e) := rfl

/-- A deterministic compiler fragment checks a Boolean property and preserves the
value bank and accumulated sign for every following instruction stream. -/
def Checks (s : Stmt) (e : List ℕ) (test : (ℕ → Bool) → Bool) : Prop :=
  ∀ (ops : List Op) (f : Flags) (v : List Bool),
    value (s.expand e ++ ops) f v = value ops ⟨f.ok && test (lookup v), f.minus⟩ v

/-- A single expression guard checks precisely its truth value. -/
theorem term_checks (a : Term) (e : List ℕ) : Checks a.guard e (fun bank => a.eval e bank) :=
  a.value_guard e

private theorem flat_checks {α : Type*} (rows : List α) (emit : α → List Op)
    (test : α → (ℕ → Bool) → Bool)
    (h : ∀ i ∈ rows, ∀ ops (f : Flags) v, value (emit i ++ ops) f v =
      value ops ⟨f.ok && test i (lookup v), f.minus⟩ v) (ops : List Op) (f : Flags) (v : List Bool) :
    value (rows.flatMap emit ++ ops) f v =
      value ops ⟨f.ok && rows.all (fun i => test i (lookup v)), f.minus⟩ v := by
  induction rows generalizing f with
  | nil => simp
  | cons i is ih =>
    simp only [List.flatMap_cons, List.append_assoc, List.all_cons]
    rw [h i (by simp)]
    rw [ih (fun x hx => h x (by simp [hx]))]
    simp [Bool.and_assoc]

/-- Repeating a guard over an interval checks all copies in their original order. -/
theorem loop_checks (b : NatExpr) (s : Stmt) (e : List ℕ) (test : ℕ → (ℕ → Bool) → Bool)
    (h : ∀ i < b.eval e, Checks s (i :: e) (test i)) :
    Checks (.loop b s) e (fun bank => (List.range (b.eval e)).all fun i => test i bank) :=
  fun ops f v => flat_checks (List.range (b.eval e)) (fun i => s.expand (i :: e)) test
    (fun i hi => h i (List.mem_range.mp hi)) ops f v

/-- Concatenating a list of guard fragments conjoins their checks. -/
theorem sequence_checks {α : Type*} (xs : List α) (s : α → Stmt) (e : List ℕ)
    (test : α → (ℕ → Bool) → Bool) (h : ∀ x ∈ xs, Checks (s x) e (test x)) :
    Checks (sequence (xs.map s)) e (fun bank => xs.all fun x => test x bank) := by
  intro ops f v
  rw [expand_sequence, List.flatMap_map]
  exact flat_checks xs _ test h ops f v

/-- One generator row handles every copy and lane of a zero-pinned range. -/
def zeroRow (copies lanes : ℕ) (p : Port) : Stmt :=
  .loop (.lit copies) (.loop (.lit lanes) ((Term.wire (p.expr (.index 1) (.index 0))).not.guard))

/-- One generator row joins two repeated ranges lane for lane. -/
def equalRow (copies lanes : ℕ) (p q : Port) : Stmt :=
  .loop (.lit copies) (.loop (.lit lanes)
    ((Term.wire (p.expr (.index 1) (.index 0))).equal (.wire (q.expr (.index 1) (.index 0)))).guard)

/-- Acceptance of the emitted zero-pinning instructions is equivalent to the
pointwise condition on all designated addresses. -/
theorem zeroRow_correct (copies lanes : ℕ) (p : Port) (e : List ℕ) :
    Checks (zeroRow copies lanes p) e
      (fun bank => (List.range copies).all fun i => (List.range lanes).all fun k => !(bank (p.atBit i k))) := by
  apply loop_checks
  intro i _
  apply loop_checks
  intro k _
  apply term_checks

/-- Compiled equality rows test all designated bit equalities and leave every wire intact. -/
theorem equalRow_correct (copies lanes : ℕ) (p q : Port) (e : List ℕ) :
    Checks (equalRow copies lanes p q) e
      (fun bank => (List.range copies).all fun i => (List.range lanes).all fun k =>
        decide (bank (p.atBit i k) = bank (q.atBit i k))) := by
  apply loop_checks
  intro i _
  apply loop_checks
  intro k _
  simpa only [Term.eval_equal, Term.eval, Port.eval_expr, NatExpr.eval, List.getD_cons_zero,
    List.getD_cons_succ] using term_checks
    ((Term.wire (p.expr (.index 1) (.index 0))).equal (.wire (q.expr (.index 1) (.index 0)))) (k :: i :: e)

/-- The Boolean zero test is the semantic zero-pin record. -/
theorem zero_checks_iff (copies lanes : ℕ) (p : Port) (bank : ℕ → Bool) :
    ((List.range copies).all fun i => (List.range lanes).all fun k => !(bank (p.atBit i k))) =
      true ↔ zeroValid bank copies lanes p := by simp [zeroValid]

/-- The Boolean wire-pairing test is the semantic interval equality. -/
theorem equal_checks_iff (copies lanes : ℕ) (p q : Port) (bank : ℕ → Bool) :
    ((List.range copies).all fun i => (List.range lanes).all fun k =>
      decide (bank (p.atBit i k) = bank (q.atBit i k))) = true ↔ equalValid bank copies lanes p q := by
  simp [equalValid]

end CellSparse

end BorderVNP
end Computability
end OAI
