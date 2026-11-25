import OAI.Optimization.LinearProgramming.Compression.DetCircuit
import OAI.Optimization.LinearProgramming.Compression.CircuitLayers
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-! The row-major program for one determinant over an ordered field. Every instruction in
its output is an instruction of the scalar RAM. Earlier layers are materialized before
any instruction reads the next layer. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM
open scoped BigOperators

/-- Read a square input matrix from its consecutive scalar registers. -/
def matrixAt {K : Type} (n : ℕ) (s : State K) (input : ℕ) : Matrix (Fin n) (Fin n) K :=
  fun i j => s.data (input + (finProdFinEquiv (i, j)).val)

def flat {K : Type} {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (q : Fin (n*n)) : K :=
  A (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

def flatBird {n : ℕ} (q : Fin (n*n)) : ArithExpr (BirdRead n) :=
  birdStepExpr (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

def inputCell {n : ℕ} (input : ℕ) (ij : Fin n × Fin n) : ℕ :=
  input + (finProdFinEquiv ij).val

def layerCell {n : ℕ} (ij : Fin n × Fin n) : Fin (n*n) := finProdFinEquiv ij

theorem flat_matrixAt {K : Type} (n : ℕ) (s : State K) (input : ℕ) (q : Fin (n*n)) :
    flat (matrixAt n s input) q = s.data (input + q.val) := by
  exact congrArg (fun z : Fin (n*n) => s.data (input + z.val)) (finProdFinEquiv.apply_symm_apply q)

private theorem flat_eval {K : Type} [CommRing K] {n : ℕ} (A F : Matrix (Fin n) (Fin n) K) :
    evalLayer layerCell flatBird (fun ij => A ij.1 ij.2) (flat F) = flat (birdStage A F) := by
  funext q
  simp only [evalLayer, flatBird, flat, birdStage, Matrix.of_apply]
  congr 1
  funext x
  rcases x with ij | ij
  · rfl
  · change flat F (finProdFinEquiv ij) = F ij.1 ij.2
    unfold flat
    rw [Equiv.symm_apply_apply]

theorem flat_eval_iter {K : Type} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (t : ℕ) :
    ((evalLayer layerCell flatBird (fun ij => A ij.1 ij.2))^[t] (flat A)) =
      flat ((birdStage A)^[t] A) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, flat_eval]

def correctSign (k : ℕ) : ArithExpr Unit :=
  if Even k then .read () else .neg (.read ())

theorem eval_correctSign {K : Type} [Ring K] (k : ℕ) (x : K) :
    (correctSign k).eval (fun _ => x) = (-1 : K)^k * x := by
  by_cases h : Even k <;> simp [correctSign, h, ArithExpr.eval, neg_one_pow_eq_ite]

/-- The answer is placed just past the tables, including at dimension zero. -/
def detResult (n out : ℕ) : ℕ := out + (n-1)*(n*n)

/-- Compile the consecutive row-major Bird tables, then copy or negate the final entry. -/
def detCircuit : (n input out : ℕ) → Program
  | 0, _, out => (ArithExpr.one : ArithExpr Empty).compile (nofun) out
  | k+1, input, out =>
    let n := k+1
    let initial (i : Fin (n*n)) := input + i.val
    compileIterLayer (inputCell (n := n) input) layerCell flatBird k initial out ++
      (correctSign k).compile (fun _ => layerResultAddr initial out k (finProdFinEquiv (0, 0)))
        (detResult n out)

private theorem sum_birdFlat_size_le (n : ℕ) :
    ∑ i : Fin (n*n), (flatBird i).size ≤ n^2 * (6*(n+1)) := by
  calc
    _ ≤ ∑ _i : Fin (n*n), 6*(n+1) := Finset.sum_le_sum fun i _ => size_birdStepExpr _ _
    _ = _ := by simp [pow_two]

/-- Number of actual scalar RAM instructions in the generated block. -/
theorem detCircuit_length_le (n input out : ℕ) :
    (detCircuit n input out).length ≤ 16*(n+1)^4 := by
  cases n with
  | zero => norm_num [detCircuit, ArithExpr.compile]
  | succ k =>
    let n := k+1
    let initial (i : Fin (n*n)) := input + i.val
    have hc := compileIterLayer_length_le (inputCell (n := n) input) layerCell flatBird k initial out
    have hsum := sum_birdFlat_size_le n
    have hs : (correctSign k).size ≤ 2 := by unfold correctSign; split <;> decide +revert
    have hlen := (correctSign k).compile_length_le
      (fun _ => layerResultAddr initial out k (finProdFinEquiv (0, 0))) (detResult n out)
    simp only [detCircuit, List.length_append]
    refine (Nat.add_le_add hc hlen).trans ?_
    have hu := Nat.mul_le_mul_left k (Nat.mul_le_mul_left 2 hsum)
    have hv := Nat.mul_le_mul_left 2 hs
    refine (Nat.add_le_add hu hv).trans ?_
    dsimp only [n]
    nlinarith [Nat.zero_le (k^3), Nat.zero_le (k^2)]

theorem prevCell_lt_end {n : ℕ} (init : Fin (n*n) → ℕ) (out k : ℕ)
    (q : Fin (n*n)) (hini : ∀ i, init i < out) :
    layerResultAddr init out k q < out + k*(n*n) := by
  cases k with
  | zero => simpa [layerResultAddr] using hini q
  | succ k =>
    have hq := q.isLt
    simp only [layerResultAddr, Nat.succ_mul]
    omega

/-- The circuit runs from every live state with disjoint input and workspace. It writes
    the determinant and preserves every scalar register below `out`. -/
theorem detCircuit_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (n input out : ℕ) (s : State K) (hs : s.output = none) (hfresh : input + n*n ≤ out) :
    ∃ t, BlockExec (detCircuit n input out) s t ∧
      t.data (detResult n out) = (matrixAt n s input).det ∧
      (∀ j < out, t.data j = s.data j) ∧ t.index = s.index ∧ t.output = none := by
  cases n with
  | zero =>
    simpa [detCircuit, detResult, ArithExpr.eval] using
      (ArithExpr.one : ArithExpr Empty).compile_spec (nofun) out s hs (nofun)
  | succ k =>
    let n := k+1
    let init (q : Fin (n*n)) := input + q.val
    let A := matrixAt n s input
    let q0 : Fin (n*n) := finProdFinEquiv (0, 0)
    have hinit (i : Fin (n*n)) : init i < out := by
      have h := i.isLt
      dsimp only [init, n] at *
      omega
    have hfix (ij : Fin n × Fin n) : inputCell input ij < out := hinit (finProdFinEquiv ij)
    obtain ⟨u, hblock, hvalues, hlow, hindex, hu⟩ :=
      compileIterLayer_spec (inputCell input) layerCell flatBird k init out s hs hfix hinit
    have hfirst : u.data (layerResultAddr init out k q0) = ((birdStage A)^[k] A) 0 0 := by
      have hi : (fun q => s.data (init q)) = flat A := funext (fun q => (flat_matrixAt n s input q).symm)
      have h := hvalues q0
      rw [hi] at h
      change u.data _ = ((evalLayer layerCell flatBird (fun ij => A ij.1 ij.2))^[k] (flat A)) q0 at h
      rw [flat_eval_iter] at h
      simpa [q0, flat] using h
    have hend : detResult n out = out + k*(n*n) := by simp [detResult, n]
    have hread (x : Unit) : layerResultAddr init out k q0 < detResult n out :=
      hend ▸ prevCell_lt_end init out k q0 hinit
    obtain ⟨t, hsign, hres, hlows, hidx, ht⟩ := (correctSign k).compile_spec
      (fun _ => layerResultAddr init out k q0) (detResult n out) u hu hread
    refine ⟨t, hblock.append hsign, ?_, ?_, hidx.trans hindex, ht⟩
    · rw [eval_correctSign, hfirst] at hres
      exact hres.trans (det_from_birdStages A).symm
    · intro j hj
      exact (hlows j (hend ▸ by omega)).trans (hlow j hj)

end Compression
end LinearProgramming
end Optimization
end OAI
