import OAI.Optimization.LinearProgramming.PriceGame.TrialMarketFractionSize
import OAI.Optimization.LinearProgramming.PriceGame.ControlEncodingPackets

/-! Concrete weight and allocation arrays in the serialized trial packets. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire

open ExactQuantumFactoring.BitStackProgram
open TrialExecution States.Mass

theorem actualWeights_fit {n count width : ℕ} (w : Fin n → ℚ) (hc : n ≤ count)
    (hw : ∀ e, 2 * RAM.ratBits (w e) + 4 ≤ width) :
    RowFits count width (List.ofFn w) := by
  refine ⟨by simpa using hc, ?_⟩
  intro x hx
  obtain ⟨e, rfl⟩ := List.mem_ofFn.mp hx
  exact (rat_le_machine _).trans (hw e)

theorem actualWeightTable_length {n B : ℕ} (w : Fin n → ℚ) (hp : ∀ e, RAM.ratBits (w e) ≤ B) :
    (listCode ratCode (List.ofFn w)).length ≤ n*(4*B+10)+1 := by
  have h := row_le (actualWeights_fit w le_rfl (fun e =>
    show 2 * RAM.ratBits (w e) + 4 ≤ 2*B+4 by have := hp e; omega))
  change (listCode ratCode (List.ofFn w)).length ≤ _
  calc
    _ ≤ rowBound n (2*B+4) := h
    _ = _ := by unfold rowBound listBound; ring

theorem actualTable_fit {N l count width : ℕ} (f : Vertex N l → ℚ)
    (hc : N*2^l ≤ count) (hw : ∀ i, 2*RAM.ratBits (f i)+4 ≤ width) :
    RowFits count width (packTable N l f) := by
  refine ⟨by simpa [packTable] using hc, ?_⟩
  intro q hq
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
  exact (rat_le_machine _).trans (hw _)

/-- Length charged for the stack input with its real path history and complete weight table. -/
theorem Envelope.codeInput_fits (env : Envelope) {N ne l : ℕ} (h : History N) (w : Weights ne)
    (hl : l ≤ env.depth) (he : ne ≤ env.experts) (hV : ∀ j < l, N*2^j ≤ env.vertices)
    (hh : ∀ j < l, ∀ v, 2*RAM.ratBits (h j v)+4 ≤ env.width)
    (hw : ∀ k, 2*RAM.ratBits (w k)+4 ≤ env.width) :
    env.InputFits (Trial.codeInput l h w) := by
  refine ⟨hl, ⟨?_, ?_⟩, actualWeights_fit w he hw⟩
  · simpa [Trial.codeInput, packHistory] using hl
  · intro xs hxs
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hxs
    exact actualTable_fit _ (hV j j.isLt) (hh j j.isLt)

/-- The final branch serializes the empty allocation matrix. -/
theorem Envelope.codeFinal_fits (env : Envelope) {N ne l : ℕ} (y : Prices N l) (dw : Weights ne)
    (hv : N*2^l ≤ env.vertices) (he : ne ≤ env.experts)
    (hy : ∀ i, 2*RAM.ratBits (y i)+4 ≤ env.width)
    (hdw : ∀ k, 2*RAM.ratBits (dw k)+4 ≤ env.width) :
    env.PreparedFits (Trial.codeFinal y dw) :=
  ⟨actualTable_fit y hv hy, ⟨Nat.zero_le _, fun _ hin => False.elim (List.not_mem_nil hin)⟩,
    actualWeights_fit dw he hdw⟩

/-- Every encoded allocation row, including its per-element delimiters, is charged
from the common input denominator and the bounds on the actual local weight registers. -/
theorem Envelope.codeProbe_fits (env : Envelope) {N ne l : ℕ} (experts : Fin ne → Expert N)
    (history : History N) (L dw : Weights ne) (hL : ∀ e, 0 ≤ L e) (Q d B : ℕ)
    (hQ : 0 < Q) (hd : Q ≤ 2^d) (hlocal : ∀ e, (L e).den ∣ Q ∧ RAM.ratBits (L e) ≤ B)
    (hv : N*2^l ≤ env.vertices) (he : ne ≤ env.experts)
    (hy : ∀ i, 2*RAM.ratBits ((marketSolverAtCommonWeightUnit experts l history L hL).prices i)+4 ≤ env.width)
    (hfrac : 2*(3+2*(B+d))+4 ≤ env.width) (hdw : ∀ k, 2*RAM.ratBits (dw k)+4 ≤ env.width) :
    env.PreparedFits (Trial.codeProbe (marketSolverAtCommonWeightUnit experts l history L hL) dw) := by
  let A := marketSolverAtCommonWeightUnit experts l history L hL
  refine ⟨actualTable_fit A.prices hv hy, ⟨?_, ?_⟩, actualWeights_fit dw he hdw⟩
  · simpa [Trial.codeProbe] using he
  · intro row hrow
    obtain ⟨e, rfl⟩ := List.mem_ofFn.mp hrow
    apply actualTable_fit _ hv
    intro i
    have hf := (market_fraction_gain_of_registers experts history L hL Q d B hQ hd hlocal
      e (fun _ => false)).1 (some i)
    omega

end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
