import OAI.Computability.BorderVNP.CellStructured
import OAI.Computability.BorderVNP.CellSparseGenerator
import OAI.Computability.RationalHitting.SignedArithmetic

/-! # A fixed private machine for arithmetic addresses of bounded syntactic depth

A bounded expression is serialized as a binary tree of fixed depth, with ordinary binary
literals and lexical loop indices. All leaves and operators are data. One program handles
every expression of that depth, including data-dependent literals and nested-loop values.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Address

open CellSparse RationalHitting.StackLanguage

/-- First three bits distinguish literal, index, sum, product and difference. -/
abbrev Header := Bool × Bool × Bool × ℕ × Unary

/-- Fixed-depth layout. The literal field is binary; the lexical variable index is unary. -/
def Layout : ℕ → Type
  | 0 => Header
  | d+1 => Header × (Layout d × Layout d)

instance layoutCoding (d : ℕ) : Coding (Layout d) := by
  induction d with
  | zero => exact inferInstanceAs (Coding Header)
  | succ d ih => exact inferInstanceAs (Coding (Header × (Layout d × Layout d)))

/-- Actual syntactic depth needed for an expression. -/
def depth : NatExpr → ℕ
  | .lit _ | .index _ => 0
  | .add a b | .mul a b | .sub a b => max (depth a) (depth b) + 1

private def fields : NatExpr → Header
  | .lit n => (false, false, false, n, ⟨0⟩)
  | .index k => (false, true, false, 0, ⟨k⟩)
  | .add .. => (true, false, false, 0, ⟨0⟩)
  | .mul .. => (true, true, false, 0, ⟨0⟩)
  | .sub .. => (true, true, true, 0, ⟨0⟩)

private def children : NatExpr → NatExpr × NatExpr
  | .add a b | .mul a b | .sub a b => (a,b)
  | _ => (.lit 0,.lit 0)

/-- Serialization uses padding only at the fixed syntactic depth of the arithmetic template. -/
def pack : (d : ℕ) → NatExpr → Layout d
  | 0, e => fields e
  | d+1, e => (fields e, pack d (children e).1, pack d (children e).2)

/-- Inputs from a sparse cell fragment and its current loop counters. -/
abbrev Input (d : ℕ) := Layout d × List ℕ

private def leaf (h : Header) (env : List ℕ) : ℕ :=
  if h.2.1 then (env.drop h.2.2.2.2.val).headD 0 else h.2.2.2.1

/-- Numeric value read from a padded descriptor and its current lexical counter bank. -/
def eval : (d : ℕ) → Input d → ℕ
  | 0, (h, env) => leaf h env
  | d+1, ((h,l,r), env) =>
    if h.1 then
      let x := eval d (l, env)
      let y := eval d (r, env)
      if h.2.1 then if h.2.2.1 then x-y else x*y else x+y
    else leaf h env

/-- The expression evaluator reads the actual literals and lexical counters at every node. -/
theorem eval_pack {d : ℕ} (e : NatExpr) (env : List ℕ) (hd : depth e ≤ d) :
    eval d (pack d e, env) = e.eval env := by
  induction d generalizing e with
  | zero =>
    cases e <;> simp_all [depth, eval, pack, fields, leaf, NatExpr.eval]
  | succ d ih =>
    cases e <;> simp_all [depth, eval, pack, fields, children, leaf, NatExpr.eval]

private theorem nat_sub : Poly (fun a : ℕ × ℕ => a.1-a.2) := by
  apply (Poly.positivePart_poly.comp Poly.natDifference).of_eq
  intro ⟨a,b⟩
  by_cases hab : a < b
  · simp [positivePart, show (a:ℤ)-b < 0 by omega, Nat.sub_eq_zero_of_le hab.le]
  · simp [positivePart, show ¬(a:ℤ)-b < 0 by omega]
    omega

private theorem leaf_poly : Poly (fun x : Header × List ℕ => leaf x.1 x.2) := by
  unfold leaf
  apply Poly.cond (by fun_prop) _ (by fun_prop)
  exact (Poly.listGetD (0:ℕ)).comp (show Poly (fun x : Header × List ℕ => (x.1.2.2.2.2,x.2)) by fun_prop)

/-- Concrete stack procedures built from the checked binary arithmetic, list and conditional
programs. The syntactic depth fixes the procedure before the private input is supplied. -/
theorem feasible (d : ℕ) : Poly (eval d) := by
  induction d with
  | zero => exact leaf_poly
  | succ d ih =>
    change Poly (fun x : (Header × (Layout d × Layout d)) × List ℕ =>
      if x.1.1.1 then
        if x.1.1.2.1 then
          if x.1.1.2.2.1 then eval d (x.1.2.1,x.2)-eval d (x.1.2.2,x.2)
          else eval d (x.1.2.1,x.2)*eval d (x.1.2.2,x.2)
        else eval d (x.1.2.1,x.2)+eval d (x.1.2.2,x.2)
      else leaf x.1.1 x.2)
    have hl : Poly (fun x : (Header × (Layout d × Layout d)) × List ℕ => eval d (x.1.2.1,x.2)) :=
      ih.comp (by fun_prop)
    have hr : Poly (fun x : (Header × (Layout d × Layout d)) × List ℕ => eval d (x.1.2.2,x.2)) :=
      ih.comp (by fun_prop)
    exact Poly.cond (by fun_prop)
      (Poly.cond (by fun_prop) (Poly.cond (by fun_prop) (nat_sub.comp (hl.pair hr))
        (Poly.natMul.comp (hl.pair hr))) (Poly.natAdd.comp (hl.pair hr)))
      (leaf_poly.comp (show Poly (fun x : (Header × (Layout d × Layout d)) × List ℕ => (x.1.1,x.2)) by fun_prop))

/-- The same finite private program runs on all sparse expression/loop environments at this
depth. Its input and output registers are clean, and its cost is polynomial in the binary
description length. -/
theorem machine (d : ℕ) :
    ∃ (p : Procedure (Coding.code : Input d → List Bool) Nat.bits (eval d)),
    ∀ (e : NatExpr) (env : List ℕ), depth e ≤ d →
      ∃ t ≤ 2*p.bound.eval ((Coding.code (pack d e,env)).length+1),
        (Structured.lower p.program).Runs t (single p.input (Coding.code (pack d e,env)))
          (single p.output (e.eval env).bits) := by
  obtain ⟨p⟩ := feasible d
  refine ⟨p, fun e env hd => ?_⟩
  obtain ⟨t, ht, h⟩ := p.correct (pack d e, env)
  obtain ⟨k, hk, hr⟩ := Structured.run h
  rw [eval_pack e env hd] at hr
  exact ⟨k, hk.trans (Nat.mul_le_mul_left _ ht), hr⟩

end CellMacro.Address

end BorderVNP
end Computability
end OAI
