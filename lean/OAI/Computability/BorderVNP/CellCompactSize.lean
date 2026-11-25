import OAI.Computability.BorderVNP.CellTermCost
import Mathlib.Data.Nat.Size

/-! # Binary descriptor length for the private bounded-loop language

Each syntax node has a fixed tag and at most one binary numeric field. A loop
contributes one copy of its body, independent of the run-time iteration count.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro

/-- Number of nodes in an address expression, with binary fields counted as leaves. -/
def NatExpr.mass : NatExpr → ℕ
  | .lit _ | .index _ => 1
  | .add a b | .mul a b | .sub a b => 1+a.mass+b.mass

/-- Largest numeral or lexical depth in an address expression. -/
def NatExpr.field : NatExpr → ℕ
  | .lit n | .index n => n
  | .add a b | .mul a b | .sub a b => max a.field b.field

/-- Node count in the serialized command tree; address subtrees are included. -/
def Stmt.mass : Stmt → ℕ
  | .nil | .fixed _ => 1
  | .read a => 1+a.mass
  | .bit a i => 1+a.mass+i.mass
  | .seq a b => 1+a.mass+b.mass
  | .loop a s => 1+a.mass+s.mass
  | .ifEq a b s t => 1+a.mass+b.mass+s.mass+t.mass

/-- Largest binary literal in the finite descriptor. -/
def Stmt.field : Stmt → ℕ
  | .nil => 0
  | .fixed (.read j) => j
  | .fixed _ => 0
  | .read a => a.field
  | .bit a b => max a.field b.field
  | .seq a b => max a.field b.field
  | .loop a b => max a.field b.field
  | .ifEq a b s t => max (max a.field b.field) (max s.field t.field)

/-- The self-delimiting field uses two symbols per binary digit and an end marker. -/
theorem encodeNat_length (n : ℕ) : (encodeNat n).length = 2*n.size+1 := by
  have h (xs : List Bool) : (xs.flatMap (fun b => [true,b])).length = 2*xs.length := by
    induction xs with
    | nil => rfl
    | cons b xs ih => simp [ih,Nat.mul_succ]
  simp [encodeNat,h,Nat.size_eq_bits_len]

private theorem nat_code_le (a : NatExpr) (M : ℕ) (h : a.field ≤ M) :
    a.code.length ≤ a.mass * (2*M.size+10) := by
  induction a with
  | lit n | index n =>
    change n ≤ M at h
    have hs := Nat.size_le_size h
    simp [NatExpr.code, NatExpr.mass, encodeNat_length]; omega
  | add a b ha hb | sub a b ha hb | mul a b ha hb =>
    obtain ⟨h₁,h₂⟩ := max_le_iff.mp h
    have he := ha h₁
    have hf := hb h₂
    simp [NatExpr.code,NatExpr.mass,Nat.add_mul]; omega

private theorem stmt_code_le (s : Stmt) (M : ℕ) (h : s.field ≤ M) :
    s.code.length ≤ s.mass * (2*M.size+10) := by
  induction s with
  | nil => simp [Stmt.code,Stmt.mass]
  | fixed op =>
    cases op <;> simp [Stmt.code,Stmt.mass,Op.bits,NatExpr.code,encodeNat_length]
    case read k => exact (by have := Nat.size_le_size (show k ≤ M from h); omega)
  | read a =>
    have hh := nat_code_le a M h
    simp [Stmt.code,Stmt.mass,Nat.add_mul]; omega
  | bit a b =>
    obtain ⟨h₁,h₂⟩ := max_le_iff.mp h
    have e := nat_code_le a M h₁
    have f := nat_code_le b M h₂
    simp [Stmt.code,Stmt.mass,Nat.add_mul]; omega
  | seq a b ha hb =>
    obtain ⟨h₁,h₂⟩ := max_le_iff.mp h
    have e := ha h₁
    have f := hb h₂
    simp [Stmt.code,Stmt.mass,Nat.add_mul]; omega
  | loop a b hb =>
    obtain ⟨h₁,h₂⟩ := max_le_iff.mp h
    have e := nat_code_le a M h₁
    have f := hb h₂
    simp [Stmt.code,Stmt.mass,Nat.add_mul]; omega
  | ifEq a b s t hs ht =>
    obtain ⟨hab,hst⟩ := max_le_iff.mp h
    obtain ⟨h₁,h₂⟩ := max_le_iff.mp hab
    obtain ⟨h₃,h₄⟩ := max_le_iff.mp hst
    have e := nat_code_le a M h₁
    have f := nat_code_le b M h₂
    have g := hs h₃
    have j := ht h₄
    simp [Stmt.code,Stmt.mass,Nat.add_mul]; omega

/-- Binary public descriptor size is linear in static syntax times the binary
length of the largest numeric field. -/
theorem Stmt.code_length_le (s : Stmt) : s.code.length ≤ s.mass*(2*s.field.size+10) :=
  stmt_code_le s _ le_rfl

/-- Static size of a list of compiled fragments counts only their single copies. -/
theorem mass_sequence (xs : List Stmt) : (sequence xs).mass = xs.length + (xs.map Stmt.mass).sum + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sequence,Stmt.mass] at ih ⊢; omega

/-- Boolean syntax including all named arithmetic address expressions. -/
def Term.mass : Term → ℕ
  | .lit _ => 1
  | .wire a => 1+a.mass
  | .paramBit a b => 1+a.mass+b.mass
  | .not a => 1+a.mass
  | .and a b | .or a b => 1+a.mass+b.mass

/-- The compiled syntax contains only a constant number of nodes per source node,
even inside an expression with dynamic addresses. -/
theorem Term.emit_mass_le (t : Term) (d : ℕ) : (t.emit d).mass ≤ 14*t.mass := by
  induction t generalizing d with
  | lit b => simp [emit,Stmt.mass,Term.mass]
  | wire a => simp [emit,Stmt.mass,Term.mass,NatExpr.mass]; omega
  | paramBit a b => simp [emit,Stmt.mass,Term.mass]
  | not a ha =>
    have h := ha d
    simp [emit,Term.mass,Stmt.mass,flip]; omega
  | and a b ha hb | or a b ha hb =>
    have he := ha d
    have hf := hb (d+1)
    simp [emit,Term.mass,Stmt.mass,mass_sequence,flip]; omega

/-- Compiling a guard adds its test and sequence nodes to the local expression. -/
theorem Term.guard_mass_le (t : Term) : t.guard.mass ≤ 14*t.mass+2 := by
  have h := t.emit_mass_le 0
  simp [guard,Stmt.mass]; omega

end CellSparse

end BorderVNP
end Computability
end OAI
