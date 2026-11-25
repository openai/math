import OAI.Computability.BorderVNP.CellFactorEmit
import OAI.Computability.BorderVNP.CellCQFPolynomialDegree
import OAI.Computability.BorderVNP.CellCQFMeter

/-! # Printing a factor from its short local packet

One factor call receives three sweep parameters, the block's starting occurrence, base,
stride, and number of factors, the factor ordinal, and the actual factor table. It has no
pointer to the rest of the cell directory. The fixed local procedure recreates the compact
address expressions under the current loop counter and its weakened version.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit.Local

open ExactQuantumFactoring.BitStackProgram

/-- Fixed scalar arguments to one of the three site-factor passes. -/
abbrev Params := ℕ × ℕ × ℕ

/-- Starting occurrence, wire base, copy stride, and one-copy factor count. -/
abbrev BlockFields := ℕ × ℕ × ℕ × ℕ

/-- Local information supplied once to an actual one-factor call. -/
abbrev Input := (Params × BlockFields) × (ℕ × Factor)

/-- Three binary sweep parameters. -/
abbrev paramsCode := prodCode Nat.bits (prodCode Nat.bits Nat.bits)

/-- Binary scalar fields of a block. -/
abbrev fieldsCode := prodCode Nat.bits (prodCode Nat.bits (prodCode Nat.bits Nat.bits))

/-- The actual tuple encoding on the private procedure's input port. -/
abbrev code := prodCode (prodCode paramsCode fieldsCode) (prodCode Nat.bits Typed.factor)

/-- Signed evaluation, gadget range validation, and gadget multiplicity prefix checking. -/
inductive Pass where
  | signed | range | gadget
  deriving DecidableEq

/-- Exact factor statement required by the original repeated-site scan. -/
def body : Pass → Params → FactorBody
  | .signed, _ => factorBody 0
  | .range, p => fun f _ off _ => (rangeTerm p.1 off f).guard
  | .gadget, p => Gadget.stepBody p.1 p.2.1 p.2.2

/-- Symbolic occurrence index with its counter at lexical index `k`. -/
def index (x : Input) (k : ℕ) : NatExpr :=
  .add (.add (.lit x.1.2.1) (.mul (.index k) (.lit x.1.2.2.2.2))) (.lit x.2.1)

/-- Symbolic block wire offset under the same loop counter. -/
def offset (x : Input) (k : ℕ) : NatExpr :=
  .add (.lit x.1.2.2.1) (.mul (.index k) (.lit x.1.2.2.2.1))

/-- One fully fixed table-printing procedure for each pass. It reads only the local input. -/
noncomputable def printer (mode : Pass) : Statement code (fun x =>
    body mode x.1.1 x.2.2 (index x 0) (offset x 0) (.index 0)) := by
  let ctx := Procedure.first (prodCode paramsCode fieldsCode) (prodCode Nat.bits Typed.factor)
  let params := (Procedure.first paramsCode fieldsCode).comp ctx
  let p₁ := (Procedure.first Nat.bits _).comp params
  let p₂₃ := (Procedure.second Nat.bits _).comp params
  let p₂ := (Procedure.first Nat.bits Nat.bits).comp p₂₃
  let p₃ := (Procedure.second Nat.bits Nat.bits).comp p₂₃
  let bf := (Procedure.second paramsCode fieldsCode).comp ctx
  let start := (Procedure.first Nat.bits _).comp bf
  let tail := (Procedure.second Nat.bits _).comp bf
  let base := (Procedure.first Nat.bits _).comp tail
  let sc := (Procedure.second Nat.bits _).comp tail
  let stride := (Procedure.first Nat.bits Nat.bits).comp sc
  let count := (Procedure.second Nat.bits Nat.bits).comp sc
  let item := Procedure.second (prodCode paramsCode fieldsCode) (prodCode Nat.bits Typed.factor)
  let ord := (Procedure.first Nat.bits Typed.factor).comp item
  let fac := (Procedure.second Nat.bits Typed.factor).comp item
  let loopIndex k := constAddr code (.index k)
  let i k := addAddr (addAddr (litAddr start) (mulAddr (loopIndex k) (litAddr count))) (litAddr ord)
  let o k := addAddr (litAddr base) (mulAddr (loopIndex k) (litAddr stride))
  cases mode with
  | signed => exact factorBodyStmt (idx := fun x => index x 0) (Procedure.constant code Nat.bits 0) fac (o 0) (loopIndex 0)
  | range => exact rangeBodyStmt p₁ fac (o 0)
  | gadget =>
    exact gadgetStepStmt (idx := fun x => index x 0) (off := fun x => offset x 0)
      (copy := fun _ => .index 0) p₁ p₂ p₃ fac (i 1) (o 1)

/-- A uniform bound on the actual native cost and both local port words. Its degree is a
constant of the fixed finite procedure, independent of the directory, wire bank and input order. -/
theorem printer_meter (mode : Pass) : ∃ C j : ℕ, ∀ x : Input,
    (printer mode).meter x ≤ C*((code x).length+1)^j := by
  let p := printer mode
  refine ⟨4*(p.bound.eval 1+1),p.bound.natDegree+1,?_⟩
  intro x
  have hc := p.cost_pow x (Nat.le_refl _)
  have hout := p.output_length_le x
  have hb := Procedure.clock_eval_pow p.bound (code x).length
  have h1 : (code x).length+1 ≤ ((code x).length+1)^(p.bound.natDegree+1) :=
    Nat.le_self_pow (by omega) _
  have h2 : ((code x).length+1)^p.bound.natDegree ≤ ((code x).length+1)^(p.bound.natDegree+1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h3 := Nat.mul_le_mul_left (p.bound.eval 1) h2
  change p.cost x+(code x).length+_+1 ≤ _
  change _ ≤ (code x).length+p.bound.eval (code x).length at hout
  nlinarith only [hc,hout,hb,h1,h3,Nat.zero_le (p.bound.eval 1 * ((code x).length+1)^(p.bound.natDegree+1))]

end CellSparse.Packet.Emit.Local

end BorderVNP
end Computability
end OAI
