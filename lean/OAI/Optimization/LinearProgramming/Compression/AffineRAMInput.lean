import OAI.Optimization.LinearProgramming.Compression.AffineRAM
import OAI.Optimization.LinearProgramming.Compression.ProjectionAffineHeight
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-! # Input and output of the scalar affine evaluation program -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

/-- A finite vector, extended by zero when indexed using a machine address. -/
def affineInputEntry {n : ℕ} (a : Fin n → ℚ) (i : ℕ) : ℚ :=
  if h : i < n then a ⟨i, h⟩ else 0

/-- Serialize the coefficient and argument at each coordinate into consecutive
scalar cells. The constant and two scratch cells precede this payload. -/
def affineInputPairs {n : ℕ} (a x : Fin n → ℚ) : List ℚ :=
  List.ofFn fun j : Fin (2 * n) =>
    if j.val % 2 = 0 then affineInputEntry a (j.val / 2) else affineInputEntry x (j.val / 2)

@[simp] theorem affineInputPairs_length {n : ℕ} (a x : Fin n → ℚ) :
    (affineInputPairs a x).length = 2 * n := by simp [affineInputPairs]

/-- Even cells hold coefficients, including zero beyond the end of the input. -/
@[simp] theorem affineInputPairs_even {n : ℕ} (a x : Fin n → ℚ) (i : ℕ) :
    (affineInputPairs a x)[2*i]?.getD 0 = affineInputEntry a i := by
  have hm : (2 * i) % 2 = 0 := by omega
  have hd : (2 * i) / 2 = i := by omega
  by_cases hi : i < n
  · have h : 2 * i < 2 * n := by omega
    simp [affineInputPairs, h, hm, hd]
  · have h : ¬ 2 * i < 2 * n := by omega
    simp [affineInputPairs, h, affineInputEntry, hi]

/-- Odd cells hold arguments, including zero beyond the end of the input. -/
@[simp] theorem affineInputPairs_odd {n : ℕ} (a x : Fin n → ℚ) (i : ℕ) :
    (affineInputPairs a x)[2*i+1]?.getD 0 = affineInputEntry x i := by
  have hd : (2 * i + 1) / 2 = i := by omega
  by_cases hi : i < n
  · have h : 2 * i + 1 < 2 * n := by omega
    simp [affineInputPairs, h, hd]
  · have h : ¬ 2 * i + 1 < 2 * n := by omega
    simp [affineInputPairs, h, affineInputEntry, hi]

@[simp] theorem affineInputEntry_fin {n : ℕ} (a : Fin n → ℚ) (i : Fin n) :
    affineInputEntry a i = a i := by simp [affineInputEntry, i.isLt]

private theorem affineInputEntry_height {n B : ℕ} (a : Fin n → ℚ) (hB : 1 ≤ B)
    (ha : ∀ i, (a i).num.natAbs ≤ B ∧ (a i).den ≤ B) (i : ℕ) :
    (affineInputEntry a i).num.natAbs ≤ B ∧ (affineInputEntry a i).den ≤ B := by
  by_cases hi : i < n
  · simpa [affineInputEntry, hi] using ha ⟨i, hi⟩
  · simp [affineInputEntry, hi, hB]

/-- In exactly `9*n+3` steps the fixed program evaluates the finite vector
dot product with its offset. The bound includes every state and register,
including initialization, intermediate rational products, and the answer. -/
theorem affineVector_eval_trace {n B : ℕ} (a x : Fin n → ℚ) (e : ℚ)
    (ha : ∀ i, (a i).num.natAbs ≤ B ∧ (a i).den ≤ B)
    (hx : ∀ i, (x i).num.natAbs ≤ B ∧ (x i).den ≤ B)
    (he : e.num.natAbs ≤ B ∧ e.den ≤ B) :
    ∃ t : Fin (9*n+3+1) → RAM.State ℚ,
      RAM.Trace affineEvalProgram (RAM.start [n] (e :: 0 :: 0 :: affineInputPairs a x)) (9*n+3) t ∧
      (t (Fin.last _)).output = some 0 ∧ (t (Fin.last _)).data 0 = e + dotProduct a x ∧
      ∀ i, RAM.scalarBound (affineEvalBits n B) (t i) := by
  have hB : 1 ≤ B := (Rat.den_pos e).trans_le he.2
  have hzero : RAM.ratBits 0 ≤ affineEvalBits n B :=
    ratBits_affine_input n 0 ⟨by simp, by simpa using hB⟩
  have ht (i : ℕ) : RAM.ratBits (affineTapeRead (affineInputPairs a x) i) ≤ affineEvalBits n B := by
    obtain ⟨k, rfl | rfl⟩ : ∃ k, i = 2*k ∨ i = 2*k+1 := ⟨i/2, by omega⟩
    · simpa only [affineTapeRead, affineInputPairs_even] using
        ratBits_affine_input n _ (affineInputEntry_height a hB ha k)
    · simpa only [affineTapeRead, affineInputPairs_odd] using
        ratBits_affine_input n _ (affineInputEntry_height x hB hx k)
  have hprod (k : ℕ) (_ : k < n) :
      RAM.ratBits (affineTapeRead (affineInputPairs a x) (2*k) *
        affineTapeRead (affineInputPairs a x) (2*k+1)) ≤ affineEvalBits n B := by
    simp only [affineTapeRead, affineInputPairs_even, affineInputPairs_odd]
    exact (ratBits_affine_product _ _ (affineInputEntry_height a hB ha k)
      (affineInputEntry_height x hB hx k)).trans (affineEvalBits_mono (Nat.zero_le n))
  have hsum (k : ℕ) (hk : k ≤ n) :
      RAM.ratBits (affinePrefix e (affineTapeRead (affineInputPairs a x)) k) ≤ affineEvalBits n B := by
    simp only [affinePrefix, affineTapeRead, affineInputPairs_even, affineInputPairs_odd]
    apply (ratBits_affine_partial_sum (Finset.range k) (affineInputEntry a) (affineInputEntry x) e
      hB he (fun i _ => affineInputEntry_height a hB ha i)
        (fun i _ => affineInputEntry_height x hB hx i)).trans
    simpa only [Finset.card_range] using affineEvalBits_mono (B := B) hk
  obtain ⟨t, htrace, hout, hval, hsafe⟩ :=
    affineProgram_trace e (affineInputPairs a x) n (affineEvalBits n B) ht hzero hsum hprod
  refine ⟨t, htrace, hout, hval.trans ?_, hsafe⟩
  simp only [affinePrefix, affineTapeRead, affineInputPairs_even, affineInputPairs_odd,
    Finset.sum_range, affineInputEntry_fin, dotProduct]

/-- A request identified by a coefficient row of an affine family is evaluated
by the very same program. The finite-coordinate enumeration is fixed before
the run and does not depend on any of the scalar inputs. -/
theorem affineFamily_evalRat_trace {ι κ : Type*} [Fintype κ] (F : AffineFamily ι κ)
    (γ : κ → ℚ) (u : ι) {B : ℕ}
    (ha : ∀ i, (F.coefficient u i).num.natAbs ≤ B ∧ (F.coefficient u i).den ≤ B)
    (hγ : ∀ i, (γ i).num.natAbs ≤ B ∧ (γ i).den ≤ B)
    (he : (F.offset u).num.natAbs ≤ B ∧ (F.offset u).den ≤ B) :
    let n := Fintype.card κ
    let idx := (Fintype.equivFin κ).symm
    ∃ t : Fin (9*n+3+1) → RAM.State ℚ,
      RAM.Trace affineEvalProgram (RAM.start [n] (F.offset u :: 0 :: 0 ::
        affineInputPairs (F.coefficient u ∘ idx) (γ ∘ idx))) (9*n+3) t ∧
      (t (Fin.last _)).output = some 0 ∧ (t (Fin.last _)).data 0 = F.evalRat γ u ∧
      ∀ i, RAM.scalarBound (affineEvalBits n B) (t i) := by
  let idx := (Fintype.equivFin κ).symm
  obtain ⟨t, htrace, hout, hval, hsafe⟩ := affineVector_eval_trace
    (F.coefficient u ∘ idx) (γ ∘ idx) (F.offset u) (fun i => ha (idx i)) (fun i => hγ (idx i)) he
  refine ⟨t, htrace, hout, hval.trans ?_, hsafe⟩
  rw [AffineFamily.evalRat, add_comm]
  congr 1
  exact idx.sum_comp (fun i => F.coefficient u i * γ i)

end Compression
end LinearProgramming
end Optimization
end OAI
