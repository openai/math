import OAI.Computability.VPVNP.RankQueryStackCodegen
import OAI.Computability.VPVNP.RankQueryTagRouter
import OAI.Computability.VPVNP.MacaulayRowIndex

/-! # Native dispatch of an augmented Macaulay row

The first block contains the integer equations, followed by the affine slice
rows, each paired with every multiplier monomial. The last block contains the
powered monomials. One fixed register routine computes the kind of the row,
the index of its equation or pin, the ordinal of its source monomial, and the
unaltered column ordinal. All these numbers are runtime operands.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.MacaulayRowDispatch

open Dispatch BurstRAM RAMTape

/-- The row block determines which coefficient routine runs for an original equation, an affine
pin or an appended powered monomial. -/
inductive Kind | equation | affine | power deriving DecidableEq

/-- Numeric dispatch tag for a row block, numbered 0 for equations, 1 for pins and 2 for
powers. -/
def Kind.tag : Kind → ℕ | .equation => 0 | .affine => 1 | .power => 2

/-- Decoded address of a Macaulay entry, giving the row block, its local equation or pin index,
and the source and column monomial ordinals. -/
structure Address where
  /-- Row block whose coefficient routine reads this entry. -/
  kind : Kind
  /-- Index within the original equations or affine pins. The decoder uses zero in this field
  for appended powers. -/
  row : ℕ
  /-- Ordinal of the multiplier monomial for an equation or pin, or of the source monomial for
  an appended power. -/
  source : ℕ
  /-- Ordinal of the requested column monomial. -/
  column : ℕ
  deriving DecidableEq

/-- Encode the decoded address as six output words in the order tag, local row, source ordinal,
column ordinal, zero, zero. -/
def Address.fields (a : Address) : Fin 6 → ℕ := ![a.kind.tag, a.row, a.source, a.column, 0, 0]

/-- These three cases use the same contiguous row ordering as `appendRows`
and the two equation blocks of `slicedQueryData`. -/
def address (i j equations pins multiples : ℕ) : Address :=
  let all := (equations+pins)*multiples
  if i < all then
    let r := i/multiples
    if r < equations then ⟨.equation, r, i%multiples, j⟩
    else ⟨.affine, r-equations, i%multiples, j⟩
  else ⟨.power, 0, i-all, j⟩

/-- Form the eight input words from the row, column, equation count, pin count and multiplier
count, followed by three zeros. -/
def inputs (i j equations pins multiples : ℕ) : Fin 8 → ℕ := ![i,j,equations,pins,multiples,0,0,0]

private def tree : Code :=
  let i : Expr := .reg 0
  let j : Expr := .reg 1
  let eqns : Expr := .reg 2
  let pins : Expr := .reg 3
  let mult : Expr := .reg 4
  let all := (eqns+pins)*mult
  let r := i/mult
  .test (all-i) 0 (.emit ![2,0,i-all,j,0,0])
    (.test (eqns-r) 0 (.emit ![1,r-eqns,i%mult,j,0,0]) (.emit ![0,r,i%mult,j,0,0]))

private theorem tree_eq (i j equations pins multiples : ℕ) :
    tree.eval (inputs i j equations pins multiples) = (address i j equations pins multiples).fields := by
  by_cases hl : i < (equations+pins)*multiples <;> by_cases hr : i/multiples < equations
  all_goals funext a; fin_cases a <;>
    simp [tree, inputs, Code.eval, eval_sub, eval_div, eval_mod, Expr.eval, Arith.eval, address, Address.fields,
      Kind.tag, Nat.sub_eq_zero_iff_le, hl, hr, Nat.not_le.mpr, Nat.le_of_not_gt]

/-- Number of scratch registers required by the compiled row decoder. -/
abbrev cap := tree.scratch
/-- Register indices for the decoder's eight inputs, six outputs and scratch space. -/
abbrev Reg := Fin (14+cap)
/-- Physical ISA ports for the decoder's register bank, with zero public memory ports. -/
abbrev Small := RAMTape.ISA.Port (14+cap) 0

/-- Fixed register routine that decodes an augmented row and returns its block and local
indices. -/
def machine : FiniteRoutine Small := tree.physical cap

/-- Upper bound on decoder ticks from the emitted instruction count and the cost per
instruction on width-`w` words. -/
def ticks (w : ℕ) := (tree.emitFields cap (List.finRange 6)).length * (100*(w+1)^2)
/-- Sufficient word width for intermediate computations when each decoder input fits in `bits`
bits. -/
def requiredWidth (bits : ℕ) := (bits+1)*tree.wordFactor

/-- Locate one of the eight input words in the decoder's register bank. -/
def inReg := Code.inReg cap
/-- Locate one of the six decoded address words in the registers immediately following the
inputs. -/
def outReg := Code.outReg cap

/-- The output ports are numbered by `Address.fields`. Input ports preserve
both supplied ordinals and all advised row counts. -/
theorem machine_runs (i j equations pins multiples p w : ℕ)
    (bound : ∀ a, inputs i j equations pins multiples a < 2^p) (hw : requiredWidth p ≤ w)
    (rs : Reg → Word w) (hin : ∀ a, (rs (inReg a)).val = inputs i j equations pins multiples a)
    (persistent : Word w) :
    ∃ cost ≤ ticks w, ∃ out, machine.Runs cost
      (RAMTape.ISA.bank Fin.elim0 persistent rs []) (RAMTape.ISA.bank Fin.elim0 persistent out []) ∧
      (∀ a, out (inReg a) = rs (inReg a)) ∧
      ∀ a, (out (outReg a)).val = (address i j equations pins multiples).fields a := by
  simpa only [ticks, machine, inReg, outReg, tree_eq] using tree.physical_runs cap p le_rfl _ rs hw bound hin Fin.elim0 persistent

/-- Recover an equation row and the dense ordinal of its multiplier. -/
theorem original_address {equations pins multiples : ℕ} (r : Fin equations) (k : Fin multiples) (j : ℕ) :
    address (r.val*multiples+k.val) j equations pins multiples = ⟨.equation,r.val,k.val,j⟩ := by
  have hm : 0 < multiples := Nat.zero_lt_of_lt k.isLt
  have hv : r.val*multiples+k.val < (equations+pins)*multiples :=
    (by have := Nat.mul_le_mul_right multiples (show r.val+1 ≤ equations+pins by omega); rw [Nat.succ_mul] at this; omega)
  have hd : (r.val*multiples+k.val)/multiples = r.val := by
    rw [Nat.mul_comm r.val, Nat.mul_add_div hm, Nat.div_eq_of_lt k.isLt, Nat.add_zero]
  simp [address, hv, hd, r.isLt, Nat.mod_eq_of_lt k.isLt]

/-- Affine rows retain their pin index when the prefix of integer equations
is removed. -/
theorem affine_address {equations pins multiples : ℕ} (r : Fin pins) (k : Fin multiples) (j : ℕ) :
    address ((equations+r.val)*multiples+k.val) j equations pins multiples = ⟨.affine,r.val,k.val,j⟩ := by
  have hm : 0 < multiples := Nat.zero_lt_of_lt k.isLt
  have hv : (equations+r.val)*multiples+k.val < (equations+pins)*multiples :=
    by have := Nat.mul_le_mul_right multiples (show (equations+r.val)+1 ≤ equations+pins by omega); rw [Nat.succ_mul] at this; omega
  have hd : ((equations+r.val)*multiples+k.val)/multiples = equations+r.val := by
    rw [Nat.mul_comm (equations+r.val), Nat.mul_add_div hm, Nat.div_eq_of_lt k.isLt, Nat.add_zero]
  simp [address, hv, hd, Nat.mod_eq_of_lt k.isLt]

/-- The appended row reads the source monomial ordinal in the suffix. -/
theorem power_address (equations pins multiples k j : ℕ) :
    address ((equations+pins)*multiples+k) j equations pins multiples = ⟨.power,0,k,j⟩ := by
  simp [address]

end RankQuery.Stack.MacaulayRowDispatch

end VPVNP
end Computability
end OAI
