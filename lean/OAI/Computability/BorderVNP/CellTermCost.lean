import OAI.Computability.BorderVNP.CellBooleanBytecode
import Mathlib.Tactic.Linarith

/-! # Costs of Boolean tests in a private cell program

The private interpreter pays for the unary representation of every read offset.
Temporary stack positions are included in the read bound. Boolean syntax is
compiled linearly without expanding an already-emitted subterm twice.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro

/-- Number of nodes in a local Boolean expression. -/
def Term.nodes : Term → ℕ
  | .lit _ | .wire _ | .paramBit .. => 1
  | .not a => a.nodes+1
  | .and a b | .or a b => a.nodes+b.nodes+1

/-- Every named wire read by the expression lies at most at address `A`. -/
def Term.Bounded (e : List ℕ) (A : ℕ) : Term → Prop
  | .lit _ | .paramBit .. => True
  | .wire x => x.eval e ≤ A
  | .not a => a.Bounded e A
  | .and a b | .or a b => a.Bounded e A ∧ b.Bounded e A

/-- Length of the fully expanded private instruction stream in binary symbols. -/
def work (s : Stmt) (e : List ℕ) := (stream (s.expand e)).length

@[simp] theorem work_seq (a b : Stmt) (e : List ℕ) : work (.seq a b) e = work a e + work b e := by
  simp [work,Stmt.expand,stream]

@[simp] theorem work_fixed (o : Op) (e : List ℕ) : work (.fixed o) e = o.bits.length := by
  simp [work,Stmt.expand,stream]

@[simp] theorem work_flip (e : List ℕ) : work flip e = 8 := rfl

private theorem stream_flatMap {α : Type*} (l : List α) (f : α → List Op) :
    (stream (l.flatMap f)).length = (l.map fun i => (stream (f i)).length).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [stream] at ih ⊢; omega

/-- Public sequence concatenation adds the lengths of the emitted binary programs. -/
theorem work_sequence (l : List Stmt) (e : List ℕ) :
    work (sequence l) e = (l.map fun s => work s e).sum := by
  simp [work,expand_sequence,stream_flatMap]

/-- The cost of a private lexical loop is the sum over its concrete iterations. -/
theorem work_loop (bound : NatExpr) (s : Stmt) (e : List ℕ) :
    work (.loop bound s) e = ((List.range (bound.eval e)).map (fun i => work s (i::e))).sum := by
  simp [work,Stmt.expand,stream_flatMap]

/-- Uniform per-element cost implies a linear bound on the summed loop work. -/
theorem sum_map_le {α : Type*} (l : List α) (f : α → ℕ) (B : ℕ) (h : ∀ i ∈ l, f i ≤ B) :
    (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have h₁ := h x List.mem_cons_self
    have h₂ := ih (fun a ha => h _ (.tail _ ha))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]; omega

/-- Bound a compiled loop by its number of iterations times a uniform body bound. -/
theorem work_loop_le (bound : NatExpr) (s : Stmt) (e : List ℕ) (B : ℕ)
    (h : ∀ i < bound.eval e, work s (i::e) ≤ B) : work (.loop bound s) e ≤ bound.eval e * B := by
  rw [work_loop]
  simpa using sum_map_le (List.range (bound.eval e)) _ B (fun i hi => h _ (List.mem_range.mp hi))

/-- Every emitted wire read is at the true offset including all pushed scratch
values. The private binary program has the following uniform length bound. -/
theorem Term.work_emit_le (t : Term) (e : List ℕ) (A d : ℕ) (h : t.Bounded e A) :
    work (t.emit d) e ≤ t.nodes * (A+d+t.nodes+20) := by
  induction t generalizing d with
  | lit b => simp [emit,work,Stmt.expand,stream,Op.bits,nodes]
  | paramBit a i => simp [emit,work,Stmt.expand,stream,Op.bits,nodes]
  | wire a =>
    change a.eval e ≤ A at h
    simp [emit,work,Stmt.expand,stream,Op.bits,NatExpr.eval,nodes]; omega
  | not a ih =>
    rw [emit,work_seq,work_flip]
    have ha := ih d h
    simp only [nodes]; nlinarith
  | and a b ha hb | or a b ha hb =>
    have h₁ := ha d h.1
    have h₂ := hb (d+1) h.2
    simp only [emit,work_sequence,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      work_fixed,work_flip,nodes]
    change _ ≤ (a.nodes+b.nodes+1)*(A+d+(a.nodes+b.nodes+1)+20)
    simp [Op.bits]
    nlinarith

/-- In a guard, all expression operands are private instructions; the final test adds
five binary symbols and does not move an external cable. -/
theorem Term.work_guard_le (t : Term) (e : List ℕ) {A N : ℕ} (hA : t.Bounded e A) (hN : t.nodes ≤ N) :
    work t.guard e ≤ N*(A+N+20)+5 := by
  rw [guard,work_seq,work_fixed]
  have h := t.work_emit_le e A 0 hA
  have hh := Nat.mul_le_mul hN (show A+0+t.nodes+20 ≤ A+N+20 by omega)
  change _ + 5 ≤ _
  omega

/-- A conjunction or disjunction of independently bounded tests has the same
address bound as its constituent tests. -/
theorem Term.bounded_any (ts : List Term) (e : List ℕ) (A : ℕ)
    (h : ∀ t ∈ ts, t.Bounded e A) : (Term.any ts).Bounded e A := by
  induction ts with
  | nil => trivial
  | cons t ts ih => exact ⟨h _ List.mem_cons_self, ih (fun j hj => h _ (.tail _ hj))⟩

/-- Node count for a disjunction with its terminal false leaf. -/
theorem Term.nodes_any (ts : List Term) : (Term.any ts).nodes = (ts.map Term.nodes).sum + ts.length + 1 := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [Term.any,Term.nodes] at ih ⊢; omega

end CellSparse

end BorderVNP
end Computability
end OAI
