import OAI.Optimization.LinearProgramming.Compression.RequestGraphPrepare
import OAI.Optimization.LinearProgramming.Compression.RequestGraphRounding
import OAI.Optimization.LinearProgramming.Lattice.BitSelectorSize

/-! A dimension-only polynomial for the actual bit tape encoding the rounded
vector and the power-of-two request grid. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace RequestTable

open ExactQuantumFactoring.BitStackProgram
open _root_.OAI.Optimization.LinearProgramming.Lattice Lattice.Bit

def paperInputFormula {R : Type*} [CommSemiring R] (N : R) : R :=
  let d := (N+1)^6+1
  let p := 100*(N+1)^3+7
  2*(p+1)+d*(6*RequestScreen.requestRoundBitsFormula d+22)+2

noncomputable def paperInputPolynomial : Polynomial ℕ := paperInputFormula Polynomial.X

@[simp] theorem paperInputPolynomial_eval (N : ℕ) : paperInputPolynomial.eval N=paperInputFormula N := by
  simp [paperInputPolynomial,paperInputFormula,RequestScreen.requestRoundBitsFormula]

private theorem round_width_mono {d e : ℕ} (h : d≤e) :
    RequestScreen.requestRoundBitsFormula d ≤ RequestScreen.requestRoundBitsFormula e := by
  unfold RequestScreen.requestRoundBitsFormula
  dsimp only
  gcongr

theorem paper_graph_input_length_for {n : ℕ} (N : ℕ) (hn : n ≤ paperWidth N)
    (v : Fin (n+1) → ℝ) (neg : (Fin (n+1) → ℤ) → ℤ → Bool)
    (hneg : ∀ a c, neg a c=true ↔ requestForm v a+c<0) :
    (inputCode (paperGrid N,List.ofFn (roundedFor neg))).length ≤ paperInputPolynomial.eval N := by
  let L := RequestScreen.requestRoundBitsFormula (n+1)
  have h := Selector.input_length (paperGrid N) L (roundedFor neg) (by
    intro i
    have hi := (roundedFor_spec v neg hneg).1 i
    exact ⟨hi.1.trans (Nat.le_succ _),hi.2.trans (Nat.le_succ _)⟩)
  change (inputCode _).length ≤ _ at h
  apply h.trans
  rw [paperInputPolynomial_eval]
  simp only [paperGrid,Nat.size_pow]
  have hd : n+1 ≤ (N+1)^6+1 := Nat.add_le_add_right hn 1
  change 2*((paperRadius N+7)+1)+(n+1)*(6*L+22)+2 ≤
    2*((paperRadius N+7)+1)+((N+1)^6+1)*(6*RequestScreen.requestRoundBitsFormula ((N+1)^6+1)+22)+2
  have hw := round_width_mono hd
  dsimp only [L]
  gcongr

theorem paper_graph_input_length {n : ℕ} (N fuel k : ℕ) (hn : n ≤ paperWidth N) (mag : Fin (n+1) → ℚ)
    (hm : ∀ i, 0 < mag i) :
    (inputCode (paperGrid N,List.ofFn (nativeRequestRounded fuel k mag))).length ≤ paperInputPolynomial.eval N :=
  paper_graph_input_length_for N hn (fun i => requestMagnitudeProxy fuel k (mag i))
    (requestMagnitudeNegative fuel k mag) (requestMagnitudeNegative_correct fuel k mag hm)

end RequestTable
end Compression
end LinearProgramming
end Optimization
end OAI
