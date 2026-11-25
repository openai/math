import OAI.Optimization.LinearProgramming.Compression.DetCircuitBits
import OAI.Optimization.LinearProgramming.Compression.DetRam
import OAI.Optimization.LinearProgramming.Compression.CircuitLayersSafe

/-! The compiled determinant's full rational RAM trace, including the temporary registers. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
open OAI.Optimization.LinearProgramming.RAM

/-- A bound for every intermediate register at every pass of the square determinant circuit. -/
def detRegisterBits (n B : ℕ) : ℕ := 3 + (n+B+2*B*n^2+3)*(n+2)

private theorem fixedRegisterBits {n B : ℕ} {t : ℕ} (ht : t ≤ n) :
    3 + (n+B+2*B*n^2+3)*(t+2) ≤ detRegisterBits n B :=
  Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right ht 2)) 3

private theorem inputBits_le_detRegisterBits (n B : ℕ) : B ≤ detRegisterBits n B := by
  let c := n+B+2*B*n^2+3
  have h : c * 1 ≤ c * (n+2) := Nat.mul_le_mul_left c (by omega)
  have hb : B ≤ c := by dsimp [c]; omega
  change B ≤ 3 + c * (n+2)
  rw [Nat.mul_one] at h
  omega

private theorem ratBits_neg (x : ℚ) : ratBits (-x) = ratBits x := by
  simp [ratBits]

private theorem flat_birdInputs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (r : ℕ) :
    Sum.elim (fun ij : Fin n × Fin n => A ij.1 ij.2)
      (((evalLayer layerCell flatBird (fun ij => A ij.1 ij.2))^[r] (flat A)) ∘ layerCell) =
      readBird A (birdLayer A r) := by
  have hi := flat_eval_iter A r
  rw [hi]
  have hstage : birdStage A = BirdDet.Spec.stepEntry A := funext (birdStage_eq A)
  funext ij
  rcases ij with ij | ij
  · rfl
  · change flat ((birdStage A)^[r] A) (finProdFinEquiv ij) = birdLayer A r ij.1 ij.2
    rw [birdLayer_eq_iterate, hstage]
    simp [flat]

private theorem allValues_flatBird {n B : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : ∀ i j, ratBits (A i j) ≤ B) (r : ℕ) (hr : r ≤ n) (q : Fin (n*n)) :
    (flatBird q).AllValues (Sum.elim (fun ij : Fin n × Fin n => A ij.1 ij.2)
      (((evalLayer layerCell flatBird (fun ij => A ij.1 ij.2))^[r] (flat A)) ∘ layerCell))
      (fun x => ratBits x ≤ detRegisterBits n B) := by
  rw [flat_birdInputs]
  exact (allValues_birdStepExpr A hA r _ _).mono (fun _ hx => hx.trans (fixedRegisterBits hr))

/-- An ambient register budget can exceed the bound on the input block. This allows a caller
    to retain earlier registers while computing successive determinants at the same precision. -/
theorem detCircuit_safe_at (n input out B M : ℕ) (s : State ℚ) (hs : s.output = none)
    (hfresh : input+n*n ≤ out) (hstart : ∀ j, ratBits (s.data j) ≤ M)
    (hinput : ∀ i j, ratBits (matrixAt n s input i j) ≤ B) (hb : detRegisterBits n B ≤ M) :
    ∃ t, SafeBlock (fun x => ratBits x ≤ M) (detCircuit n input out) s t := by
  let P := fun x => ratBits x ≤ M
  have hzero : P 0 := by change 3 ≤ M; exact (Nat.le_add_right 3 _).trans hb
  cases n with
  | zero =>
    have hone : P 1 := by change 3 ≤ M; exact (Nat.le_add_right 3 _).trans hb
    exact (ArithExpr.one : ArithExpr Empty).compile_safe nofun out s hs nofun hstart hzero hone
  | succ k =>
    let n := k + 1
    let init (q : Fin (n*n)) := input + q.val
    let A := matrixAt n s input
    let q0 : Fin (n*n) := finProdFinEquiv (0, 0)
    have hinit (q : Fin (n*n)) : init q < out := by
      have h := q.isLt
      dsimp only [init, n] at *
      omega
    have hfix (ij : Fin n × Fin n) : inputCell input ij < out := hinit (finProdFinEquiv ij)
    have hA (i j : Fin n) : ratBits (A i j) ≤ B := hinput i j
    have hfn : (fun q => s.data (init q)) = flat A := funext (fun q => (flat_matrixAt n s input q).symm)
    have hfixedFn : (fun ij : Fin n × Fin n => s.data (inputCell input ij)) =
        (fun ij : Fin n × Fin n => A ij.1 ij.2) := by
      funext ⟨i,j⟩; rfl
    have hvals (r : ℕ) (hr : r < k) (q : Fin (n*n)) : (flatBird q).AllValues
        (Sum.elim (fun ij => s.data (inputCell input ij))
          (((evalLayer layerCell flatBird (fun ij => s.data (inputCell input ij)))^[r]
             (fun u => s.data (init u))) ∘ layerCell)) P := by
      rw [hfn, hfixedFn]
      exact (allValues_flatBird (n := n) (B := B) A hA r (by dsimp [n]; omega) q).mono
        fun _ hx => hx.trans hb
    obtain ⟨u, hsafe⟩ := compileIterLayer_safe P (inputCell input) layerCell flatBird k init out s
      hs hfix hinit hstart hzero hvals
    obtain ⟨u', hblock, _hv, _hlo, _hi, hu⟩ :=
      compileIterLayer_spec (inputCell input) layerCell flatBird k init out s hs hfix hinit
    have hsame := hsafe.toBlockExec.deterministic hblock
    subst u'
    have hend : detResult n out = out + k*(n*n) := by simp [detResult, n]
    have hread (x : Unit) : layerResultAddr init out k q0 < detResult n out :=
      hend ▸ prevCell_lt_end init out k q0 hinit
    have hvSign : (correctSign k).AllValues (fun _ => u.data (layerResultAddr init out k q0)) P := by
      unfold correctSign
      split
      · exact hsafe.last_ok _
      · refine ⟨?_, hsafe.last_ok _⟩
        change ratBits (-u.data _) ≤ _
        rw [ratBits_neg]; exact hsafe.last_ok _
    obtain ⟨t, hsign⟩ := (correctSign k).compile_safe (fun _ => layerResultAddr init out k q0)
      (detResult n out) u hu hread hsafe.last_ok hzero hvSign
    exact ⟨t, hsafe.append hsign⟩

/-- The actual RAM trace computes the determinant in a dimension-only number of instructions;
every register at every position has reduced encoding length bounded by the stated polynomial. -/
theorem detCircuit_trace_bits (n input out B : ℕ) (s : State ℚ) (pre suffix : Program)
    (hpc : s.pc = pre.length) (hs : s.output = none) (hfresh : input+n*n ≤ out)
    (hb : ∀ j, ratBits (s.data j) ≤ B) :
    let code := detCircuit n input out
    code.length ≤ 16*(n+1)^4 ∧ ∃ v : Fin (code.length+1) → State ℚ,
      Trace (pre ++ code ++ suffix) s code.length v ∧
      (v (Fin.last _)).data (detResult n out) = (matrixAt n s input).det ∧
      ∀ i, scalarBound (detRegisterBits n B) (v i) := by
  refine ⟨detCircuit_length_le .., ?_⟩
  obtain ⟨t, hsafe⟩ := detCircuit_safe_at n input out B (detRegisterBits n B) s hs hfresh
    (fun j => (hb j).trans (inputBits_le_detRegisterBits n B)) (fun i j => hb _) le_rfl
  obtain ⟨t', hblock, hres, _hs⟩ := detCircuit_spec n input out s hs hfresh
  have hsame := hsafe.toBlockExec.deterministic hblock
  subst t'
  obtain ⟨v, hrun, hlast, hok⟩ := hsafe.trace_append pre suffix hpc
  exact ⟨v, hrun, hlast ▸ hres, hok⟩

end Compression
end LinearProgramming
end Optimization
end OAI
