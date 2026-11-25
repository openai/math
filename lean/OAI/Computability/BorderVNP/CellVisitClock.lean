import OAI.Computability.BorderVNP.CellAddressLength
import OAI.Computability.BorderVNP.CellGeneratorMachine

/-! # Uniform binary cost of arithmetic during private command expansion

All occurrences use the same expression and bit procedures at fixed arithmetic depth.
A bounded lexical environment contributes only its framed binary digits to their input.
A single polynomial clock bounds both procedures, their argument lengths, and the digits
of every intermediate address returned to the branch or loop dispatcher.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Generator

open CellSparse RationalHitting RationalHitting.StackLanguage

/-- Binary width available to one visit. Lexical variable indices use unary fields. -/
def visitWidth (M U J : ℕ) := 1+M.size+U.size+J

/-- Size multiplier for a two-expression record and its lexical environment. -/
def visitScale (d h : ℕ) := 6*64^(d+1)+3*h+4

/-- A common time polynomial in the binary width, fixed before any actual command is read. -/
noncomputable def visitClock (d h : ℕ) : TimeBound :=
  (.variable + evalClock d + bitClock d).comp (.const (visitScale d h) * .variable)

/-- Every lexical word is framed separately, including a zero loop counter. -/
theorem env_length (env : List ℕ) (h U : ℕ) (he : env.length ≤ h) (hu : ∀ i ∈ env, i ≤ U) :
    (Coding.code env).length ≤ h*(2*U.size+1) := by
  apply (listCode_length_le Nat.bits env U.size ?_).trans (Nat.mul_le_mul_right _ he)
  intro i hi
  simpa only [Nat.size_eq_bits_len] using Nat.size_le_size (hu i hi)

private theorem argument_bounds {d h M U J : ℕ} {env : List ℕ} (he : env.length ≤ h)
    (hu : ∀ i ∈ env, i ≤ U) (a b : NatExpr) (ha : a.field ≤ M) (hb : b.field ≤ M)
    (ja : a.lexical ≤ J) (jb : b.lexical ≤ J) :
    (Coding.code (Address.pack d a,env)).length+1 ≤ visitScale d h * visitWidth M U J ∧
      (Coding.code ((Address.pack d a,Address.pack d b),env)).length+1 ≤ visitScale d h * visitWidth M U J := by
  let W := visitWidth M U J
  have aB (e : NatExpr) (hf : e.field ≤ M) (hj : e.lexical ≤ J) :
      (Coding.code (Address.pack d e)).length ≤ 64^(d+1)*W :=
    (Address.pack_length d e).trans (Nat.mul_le_mul_left _ (by
      have := Nat.size_le_size hf; dsimp [W,visitWidth]; omega))
  have h₁ := aB a ha ja
  have h₂ := aB b hb jb
  have hs := (env_length env h U he hu).trans (Nat.mul_le_mul_left h (show 2*U.size+1 ≤ 3*W by
    dsimp [W,visitWidth]; omega))
  have Wpos : 1 ≤ W := by dsimp [W,visitWidth]; omega
  rw [← Nat.mul_assoc, Nat.mul_comm h 3, Nat.mul_assoc] at hs
  change _ ≤ (6*64^(d+1)+3*h+4)*W ∧ _ ≤ (6*64^(d+1)+3*h+4)*W
  simp only [prod_code_length,Nat.add_mul,Nat.mul_assoc]
  omega

private theorem expr_value_le (d : ℕ) (e : NatExpr) (env : List ℕ) (hd : Address.depth e ≤ d) :
    (e.eval env).bits.length ≤ (clocks d).expr e env := by
  let p := (Address.machine d).choose
  have bound := p.size (Address.pack d e,env)
  rw [Address.eval_pack e env hd] at bound
  apply bound.trans
  change p.bound.eval _ ≤ (pairClock p).eval _
  simp only [pairClock,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_variable,TimeBound.eval_numeral]
  omega

/-- One visited expression has bounded input length, bounded clock, and a bounded binary result. -/
theorem expression_visit {d h M U J : ℕ} {env : List ℕ} (he : env.length ≤ h)
    (hu : ∀ i ∈ env, i ≤ U) (e : NatExpr) (hd : Address.depth e ≤ d) (hf : e.field ≤ M)
    (hj : e.lexical ≤ J) :
    (Coding.code (Address.pack d e,env)).length+1 ≤ (visitClock d h).eval (visitWidth M U J) ∧
    (clocks d).expr e env ≤ (visitClock d h).eval (visitWidth M U J) ∧
    (e.eval env).bits.length ≤ (visitClock d h).eval (visitWidth M U J) := by
  have input := (argument_bounds (d := d) he hu e e hf hf hj hj).1
  have cost := (evalClock d).monotone input
  have value := expr_value_le d e env hd
  change _ ≤ (evalClock d).eval _ at value
  simp only [visitClock,TimeBound.eval_comp,TimeBound.eval_add,TimeBound.eval_variable,
    TimeBound.eval_mul,TimeBound.eval_const,clocks]
  omega

/-- Extracting a bit pays for the packed pair of addresses and the shared lexical environment. -/
theorem bit_visit {d h M U J : ℕ} {env : List ℕ} (he : env.length ≤ h)
    (hu : ∀ i ∈ env, i ≤ U) (v i : NatExpr) (hv : v.field ≤ M) (hi : i.field ≤ M)
    (jv : v.lexical ≤ J) (ji : i.lexical ≤ J) :
    (Coding.code ((Address.pack d v,Address.pack d i),env)).length+1 ≤ (visitClock d h).eval (visitWidth M U J) ∧
    (clocks d).bit v i env ≤ (visitClock d h).eval (visitWidth M U J) := by
  have input := (argument_bounds (d := d) he hu v i hv hi jv ji).2
  have cost := (bitClock d).monotone input
  simp only [visitClock,TimeBound.eval_comp,TimeBound.eval_add,TimeBound.eval_variable,
    TimeBound.eval_mul,TimeBound.eval_const,clocks]
  omega

end CellMacro.Generator

end BorderVNP
end Computability
end OAI
