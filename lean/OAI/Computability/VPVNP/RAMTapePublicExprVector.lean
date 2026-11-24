import OAI.Computability.VPVNP.RAMTapePublicExprCompiler

/-! # Preparing the finite vector of public operands for the live instruction table

Registers are filled in increasing order. Each expression's private registers
lie above its result, so later evaluations preserve the preceding outputs.
After the last expression, the same finite loop writes zero to every remaining
register.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.PublicExprMachine

open BurstRAM PrivateRAM LiveProgram

variable {k r : ℕ}

/-- Largest register index used by the vector program. -/
def capacity (expr : Fin k → PublicExpr) := k + Finset.univ.sup (fun i => extra (expr i))

/-- Size of the register file allocated for evaluating the entire public expression vector. -/
abbrev registerCount (expr : Fin k → PublicExpr) := capacity expr + 1

private def term (expr : Fin k → PublicExpr) (i : Fin (registerCount expr)) :=
  if h : i.val < k then expr ⟨i.val,h⟩ else .lit 0

private theorem term_room (expr : Fin k → PublicExpr) (i : Fin (registerCount expr)) :
    i.val + extra (term expr i) ≤ capacity expr := by
  unfold term
  split
  · rename_i hi
    exact Nat.add_le_add hi.le (Finset.le_sup (f := fun j => extra (expr j)) (Finset.mem_univ _))
  · simpa [extra] using Nat.le_of_lt_succ i.isLt

private theorem term_fits (g : Geometry) (expr : Fin k → PublicExpr)
    (hf : ∀ j, (expr j).Fits g (2^g.w)) (i : Fin (registerCount expr)) :
    (term expr i).Fits g (2^g.w) := by
  unfold term
  split
  · exact hf _
  · exact ⟨Nat.two_pow_pos _, trivial⟩

private def compilePrefix (expr : Fin (r+1) → PublicExpr) : (n : ℕ) → n ≤ r+1 → FiniteRoutine (BankPort r)
  | 0, _ => .ret
  | n+1, hn => (compilePrefix expr n (by omega)).followedBy (compile r n (expr ⟨n,hn⟩))

private def maxNodes (expr : Fin (r+1) → PublicExpr) := Finset.univ.sup (fun i => nodes (expr i))

private theorem prefix_runs (g : Geometry) (expr : Fin (r+1) → PublicExpr)
    (hroom : ∀ i, i.val + extra (expr i) ≤ r) (hfits : ∀ i, (expr i).Fits g (2^g.w))
    (p : Word g.w) (rs : Fin (r+1) → Word g.w) (log : WriteLog g.w) (n : ℕ) (hn : n ≤ r+1) :
    ∃ t ≤ n * (maxNodes expr * nodeCost g.w) + 1, ∃ out : Fin (r+1) → Word g.w,
      (compilePrefix expr n hn).Runs t (ISA.bank (geometryWords g) p rs log) (ISA.bank (geometryWords g) p out log) ∧
      ∀ i : Fin (r+1), i.val < n → out i = packed g.w ((expr i).eval g) := by
  induction n with
  | zero =>
    exact ⟨1, by simp, rs, Routine.runs_ret _, fun _ h => (Nat.not_lt_zero _ h).elim⟩
  | succ n ih =>
    obtain ⟨t,ht,mid,pre,ok⟩ := ih (by omega)
    let i : Fin (r+1) := ⟨n, hn⟩
    obtain ⟨u,hu,out,one,hout,keep⟩ :=
      compile_computes g r n (expr i) (hroom i) (hfits i) p mid log
    have hs : nodes (expr i) ≤ maxNodes expr := Finset.le_sup (f := fun j => nodes (expr j)) (Finset.mem_univ i)
    have hcost := hu.trans (Nat.mul_le_mul_right (nodeCost g.w) hs)
    refine ⟨_, by rw [Nat.succ_mul]; omega, out, pre.followedBy one, ?_⟩
    intro j hj
    by_cases he : j.val = n
    · have ji : j = i := Fin.ext he
      have ai : addr r n = i := Fin.ext (addr_val (by omega))
      simpa only [ji, ai] using hout
    · exact (keep _ (by omega)).trans (ok _ (by omega))

/-- Evaluate public expressions in increasing slot order and zero the remaining registers. -/
def vector (expr : Fin k → PublicExpr) : FiniteRoutine (ISA.Port (registerCount expr) 4) :=
  compilePrefix (term expr) (registerCount expr) le_rfl

/-- Expected register contents after vector evaluation, with packed expression values in the
operand slots and zero elsewhere. -/
def output (g : Geometry) (expr : Fin k → PublicExpr) (i : Fin (registerCount expr)) : Word g.w :=
  if h : i.val < k then packed g.w ((expr ⟨i.val,h⟩).eval g) else 0

/-- The coefficient of the quadratic word-width bound depends only on the fixed expression vector. -/
def coefficient (expr : Fin k → PublicExpr) := registerCount expr * maxNodes (term expr) * 150

theorem vector_runs (g : Geometry) (expr : Fin k → PublicExpr) (hfits : ∀ i, (expr i).Fits g (2^g.w))
    (p : Word g.w) (rs : Fin (registerCount expr) → Word g.w) (log : WriteLog g.w) :
    ∃ t ≤ coefficient expr * (g.w+1)^2 + 1, (vector expr).Runs t
      (ISA.bank (geometryWords g) p rs log) (ISA.bank (geometryWords g) p (output g expr) log) := by
  obtain ⟨t,ht,out,run,ho⟩ := prefix_runs g (term expr) (term_room expr) (term_fits g expr hfits)
    p rs log (registerCount expr) le_rfl
  have he : out = output g expr := by
    funext i
    rw [ho i i.isLt, output, term]
    split <;> rfl
  rw [he] at run
  exact ⟨t, by simpa only [nodeCost, coefficient, Nat.mul_assoc] using ht, run⟩

/-- The instruction table can address its public operands in their original order. -/
theorem output_at (g : Geometry) (expr : Fin k → PublicExpr) (i : Fin k) :
    output g expr ⟨i.val, by dsimp [registerCount, capacity]; omega⟩ =
      packed g.w ((expr i).eval g) := by simp [output, i.isLt]

end RAMTape.PublicExprMachine

end VPVNP
end Computability
end OAI
