import OAI.Computability.VPVNP.RankQueryStackCodegen
import OAI.Computability.VPVNP.RankQueryStackBounds

/-!
# Fixed bit-stack programs for matrix queries

Three shared-bank routines describe the current Schur query and generate its
left and right subqueries. A fourth computes the column index of a tagged
Gram coefficient. Every routine has a fixed table independent of the matrix
dimensions, extension field and degree ranges.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Dispatch

open BurstRAM RAMTape

private def gram : Code :=
  let row : Expr := .reg 0
  let col : Expr := .reg 1
  let degree : Expr := .reg 2
  let width : Expr := .reg 3
  let k := degree - row - 2
  let empty := Code.emit ![0,0,0,0,0,0]
  .test ((row+2)-degree) 0
    (.test ((k+1)-width) 0 (.emit ![1,row,col,k,0,0]) empty) empty

/-- Inputs to the Gram coefficient dispatch, consisting of row indices `i` and `j`, degree `z`,
column count `m`, and four zero words. -/
def gramInput (i j z m : ℕ) : Fin 8 → ℕ := ![i,j,z,m,0,0,0,0]

/-- A valid Gram request contains two row indices and the common column to
read. The remaining descriptor gives the zero coefficient. -/
def decodeGram {n m : ℕ} {F : Type*} [CommRing F] (M : Matrix (Fin n) (Fin m) F)
    (words : Fin 6 → ℕ) : F :=
  if words 0 = 1 then
    if hr : words 1 < n then if hc : words 2 < n then if hk : words 3 < m then
      M ⟨words 1,hr⟩ ⟨words 3,hk⟩ * M ⟨words 2,hc⟩ ⟨words 3,hk⟩ else 0 else 0 else 0
  else 0

theorem gram_eq {n m : ℕ} {F : Type*} [CommRing F] (M : Matrix (Fin n) (Fin m) F)
    (i j : Fin n) (z : ℕ) :
    decodeGram M (gram.eval (gramInput i j z m)) = weightedGramEntryCoeff M i j z := by
  by_cases h₁ : i.val+2 ≤ z <;> by_cases h₂ : z-i.val-2 < m
  all_goals have hs₂ : (z-i.val-2+1) ≤ m ↔ z-i.val-2 < m := by omega
  all_goals simp [gram, gramInput, decodeGram, Code.eval, Expr.eval, Arith.eval, eval_sub,
    weightedGramEntryCoeff, hs₂, h₁,h₂, Nat.sub_eq_zero_iff_le]

/-- The four dispatch operations describe a Schur query, stage either child, or decode a
weighted Gram coefficient. -/
inductive Operation where
  | describe | left | right | gram
  deriving DecidableEq

/-- Register decision tree implementing the chosen dispatch operation. -/
def Operation.tree : Operation → Code
  | .describe => VPVNP.RankQuery.Stack.Dispatch.describe
  | .left => child false
  | .right => child true
  | .gram => VPVNP.RankQuery.Stack.Dispatch.gram

theorem gram_words (i j z m : ℕ) :
    Operation.gram.tree.eval (gramInput i j z m) = if i+2 ≤ z ∧ z-i-2 < m
      then ![1,i,j,z-i-2,0,0] else ![0,0,0,0,0,0] := by
  have hs : z-i-2+1 ≤ m ↔ z-i-2 < m := by omega
  by_cases hi : i+2 ≤ z <;> by_cases hk : z-i-2 < m <;>
    funext a <;> fin_cases a <;>
    simp [Operation.tree, gram, Code.eval, Expr.eval, Arith.eval, eval_sub, gramInput,
      Nat.sub_eq_zero_iff_le, hs, hi, hk]

/-- Shared scratch-register capacity sufficient for each of the four dispatch trees. -/
def capacity := describe.scratch + (child false).scratch + (child true).scratch + gram.scratch
/-- Uniform factor bounding the word width needed by any of the four dispatch trees. -/
def widthFactor := describe.wordFactor + (child false).wordFactor + (child true).wordFactor + gram.wordFactor

private theorem Operation.scratch_le (a : Operation) : a.tree.scratch ≤ capacity := by
  cases a <;> simp only [capacity, Operation.tree] <;> omega

private theorem Operation.factor_le (a : Operation) : a.tree.wordFactor ≤ widthFactor := by
  cases a <;> simp only [widthFactor, Operation.tree] <;> omega

/-- Compile the operation's decision tree into a bit-stack routine on the shared register bank. -/
def Operation.machine (a : Operation) := a.tree.physical capacity

/-- Step bound for executing the operation and writing its six output fields at word width `w`. -/
def Operation.clock (a : Operation) (w : ℕ) :=
  (a.tree.emitFields capacity (List.finRange 6)).length * (100*(w+1)^2)

/-- Execute the complete fixed bit-stack instruction table, including binary
arithmetic, branching and all six register writes. -/
theorem Operation.run {w p : ℕ} (a : Operation) (env : Fin 8 → ℕ)
    (rs : Regs (14+capacity) w) (hw : (p+1)*widthFactor ≤ w)
    (he : ∀ i, env i < 2^p) (hr : ∀ i, (rs (Code.inReg capacity i)).val = env i)
    (pub : Fin 0 → Word w) (persistent : Word w) :
    ∃ t ≤ a.clock w, ∃ out,
      a.machine.Runs t (ISA.bank pub persistent rs []) (ISA.bank pub persistent out []) ∧
        (∀ i, out (Code.inReg capacity i) = rs (Code.inReg capacity i)) ∧
        ∀ i, (out (Code.outReg capacity i)).val = a.tree.eval env i :=
  a.tree.physical_runs _ _ a.scratch_le env rs
    ((Nat.mul_le_mul_left _ a.factor_le).trans hw) he hr _ _

theorem describe_run {n U Z w p : ℕ} {R : Type*} [CommRing R] (q : SchurKey n U Z)
    (entry : Entry n R) (k : ℕ) (rs : Regs (14+capacity) w) (hw : (p+1)*widthFactor ≤ w)
    (he : ∀ i, inputs q k i < 2^p) (hr : ∀ i, (rs (Code.inReg capacity i)).val = inputs q k i)
    (pub : Fin 0 → Word w) (persistent : Word w) :
    ∃ t ≤ Operation.describe.clock w, ∃ out, Operation.describe.machine.Runs t
      (ISA.bank pub persistent rs []) (ISA.bank pub persistent out []) ∧
      decode entry (fun i => (out (Code.outReg capacity i)).val) = (q.node entry).describe := by
  obtain ⟨t,ht,out,hrun,_,hout⟩ := Operation.describe.run _ rs hw he hr pub persistent
  exact ⟨t,ht,out,hrun,(congrArg (decode entry) (funext hout)).trans (describe_eq entry q k)⟩

theorem child_run {n U Z w p : ℕ} {R : Type*} [CommRing R] (q : SchurKey n U Z)
    (entry : Entry n R) {t : ℕ} {f : Fin t → SchurKey n U Z × SchurKey n U Z}
    (hn : q.node entry = .branch t f) (k : Fin t) (right : Bool)
    (rs : Regs (14+capacity) w) (hw : (p+1)*widthFactor ≤ w)
    (he : ∀ i, inputs q k.val i < 2^p) (hr : ∀ i, (rs (Code.inReg capacity i)).val = inputs q k.val i)
    (pub : Fin 0 → Word w) (persistent : Word w) :
    let a := if right then Operation.right else Operation.left
    ∃ s ≤ a.clock w, ∃ out, a.machine.Runs s (ISA.bank pub persistent rs []) (ISA.bank pub persistent out []) ∧
      (fun i => (out (Code.outReg capacity i)).val) = (if right then (f k).2 else (f k).1).words := by
  let a := if right then Operation.right else Operation.left
  obtain ⟨s,hs,out,hrun,_,hout⟩ := a.run _ rs hw he hr pub persistent
  have ha : a.tree = child right := by cases right <;> rfl
  rw [ha] at hout
  exact ⟨s,hs,out,hrun,(funext hout).trans (child_eq entry q hn k right)⟩

theorem gram_run {n m w p : ℕ} {R : Type*} [CommRing R] (M : Matrix (Fin n) (Fin m) R)
    (i j : Fin n) (z : ℕ) (rs : Regs (14+capacity) w) (hw : (p+1)*widthFactor ≤ w)
    (he : ∀ k, gramInput i j z m k < 2^p)
    (hr : ∀ k, (rs (Code.inReg capacity k)).val = gramInput i j z m k)
    (pub : Fin 0 → Word w) (persistent : Word w) :
    ∃ s ≤ Operation.gram.clock w, ∃ out, Operation.gram.machine.Runs s
      (ISA.bank pub persistent rs []) (ISA.bank pub persistent out []) ∧
      decodeGram M (fun k => (out (Code.outReg capacity k)).val) = ((weightedGram M) i j).coeff z := by
  obtain ⟨t,ht,out,hrun,_,hout⟩ := Operation.gram.run _ rs hw he hr pub persistent
  exact ⟨t,ht,out,hrun,(congrArg (decodeGram M) (funext hout)).trans
    ((gram_eq M i j z).trans (weightedGramEntryCoeff_eq M i j z))⟩

end RankQuery.Stack.Dispatch

end VPVNP
end Computability
end OAI
