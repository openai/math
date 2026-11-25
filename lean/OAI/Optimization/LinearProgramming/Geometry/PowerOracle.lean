import OAI.Optimization.LinearProgramming.Geometry.PowerRAM
import OAI.Optimization.LinearProgramming.Geometry.PowerGridRAM

/-! The complete scalar magnitude approximation in the geometric label test. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace PowerRAM

open RAM

/-- A dimension-independent block. Its input cells are address 0 (B) and
scalar 0 (θ), and its numeric return cell is 15. -/
def block : Block := .seq rawBlock PowerGridRAM.block

def program : Program := block.compile 0 ++ [.halt 0]

def width (H B : ℕ) (θ : ℚ) : ℕ := PowerGridRAM.width (rawWidth H B θ) (B+1)

theorem width_additive (H B : ℕ) (θ : ℚ) : width H B θ = H + width 0 B θ := by
  simp only [width, PowerGridRAM.width, rawWidth_additive H B θ, Nat.add_assoc]

/-- The same rational returned by the finite Taylor-and-grid definition is
computed using just ordinary RAM operations, including range tests, construction
of powers of two, and every dyadic decision. -/
theorem run_block (m : Memory ℚ) (H B : ℕ) (θ : ℚ) (hb : m.index 0 = B)
    (hi : m.data 0 = θ) (hθ : θ ≤ 0) (hm : ∀ j, ratBits (m.data j) ≤ H) :
    ∃ n k, k ≤ 32*B+158 ∧
      Block.Eval (fun v => ∀ j, ratBits (v.data j) ≤ width H B θ) block m k n ∧
      n.data 15 = roundedPower θ B ∧ Frame m n := by
  obtain ⟨u, k, hk, er, hcount, hraw, firstFrame⟩ := run_rawBlock m H B θ hb hi hθ hm
  let raw := if θ < -(B : ℚ) then 0 else reducedPowerApprox θ B
  obtain ⟨v, l, hl, eg, hval⟩ := PowerGridRAM.run_block u (B+1) (rawWidth H B θ) raw
    hraw hcount er.safe_end
  have h₁ := weaken er (Q := fun n => ∀ j, ratBits (n.data j) ≤ width H B θ)
    (fun _ h j => (h j).trans (by dsimp [width,PowerGridRAM.width]; omega))
  have h₂ := weaken eg (Q := fun n => ∀ j, ratBits (n.data j) ≤ width H B θ)
    (fun _ h => h.1)
  refine ⟨v,k+l,by omega,.seq h₁ h₂,?_,?_⟩
  · exact hval.trans (roundedPower_eq_quantized_raw θ B).symm
  · constructor
    · intro j hj
      exact (eg.safe_end.2.data j (by omega)).trans (firstFrame.data j hj)
    · intro j hj
      exact (eg.safe_end.2.index j (by omega)).trans (firstFrame.index j hj)

theorem width_polynomial (H B : ℕ) (θ : ℚ) :
    width H B θ ≤ 10000006 * (H + B + ratBits θ + 20)^4 := by
  let s := H+B+ratBits θ+20
  have hs : 1 ≤ s := by dsimp [s]; omega
  have h₄ : s ≤ s^4 := by simpa using Nat.pow_le_pow_right hs (show 1 ≤ 4 by decide)
  have hB : B ≤ s := by dsimp [s]; omega
  have hc : 13 ≤ s := by dsimp [s]; omega
  have h := rawWidth_polynomial H B θ
  change rawWidth H B θ ≤ 10000000*s^4 at h
  change rawWidth H B θ + 5*(B+1) + 8 ≤ 10000006*s^4
  omega

/-- Standalone input and all intermediate register files of the actual
terminated program. The arithmetic bound is independent of the size of θ. -/
theorem roundedPower_RAM (B : ℕ) (θ : ℚ) (hθ : θ ≤ 0) :
    ∃ k ≤ 32*B+159, ∃ t : Fin (k+1) → State ℚ,
      Trace program (start [B] [θ]) k t ∧
      (t (Fin.last k)).output = some 0 ∧
      (t (Fin.last k)).data 15 = roundedPower θ B ∧
      (∀ i j, ratBits ((t i).data j) ≤ 10000006*(ratBits θ+B+ratBits θ+20)^4) := by
  let s := start [B] [θ]
  have hm : ∀ j, ratBits (s.data j) ≤ ratBits θ := by
    intro j; cases j with
    | zero => exact le_rfl
    | succ j => change ratBits (0 : ℚ) ≤ ratBits θ
                change 3 ≤ 3 + _ + _
                omega
  obtain ⟨n,k,hk,e,hval,_⟩ := run_block s.memory (ratBits θ) B θ rfl rfl hθ hm
  obtain ⟨t,ht,ho,heq,hbound⟩ := e.halted_trace (tag := 0)
  refine ⟨k+1,by omega,t,ht,ho,?_,fun i j => (hbound i j).trans (width_polynomial ..)⟩
  exact (congrArg (fun mm : Memory ℚ => mm.data 15) heq).trans hval

/-- Semantic bound used for rounding the nonzero entries of the triangular
minor basis. The pivot and all values stay in the required unit interval. -/
theorem approximates_nonpositive_log (B : ℕ) (θ : ℚ) (hθ : θ ≤ 0) :
    ∃ k ≤ 32*B+159, ∃ t : Fin (k+1) → State ℚ,
      Trace program (start [B] [θ]) k t ∧ (t (Fin.last k)).output = some 0 ∧
      let x := (t (Fin.last k)).data 15
      0 ≤ x ∧ x ≤ 1 ∧ (θ = 0 → x = 1) ∧
        |(x : ℝ) - (2 : ℝ)^(θ : ℝ)| ≤ (1 / 2 : ℝ)^B ∧
        ∀ i j, ratBits ((t i).data j) ≤ 10000006*(ratBits θ+B+ratBits θ+20)^4 := by
  obtain ⟨k,hk,t,ht,ho,hr,hb⟩ := roundedPower_RAM B θ hθ
  refine ⟨k,hk,t,ht,ho,?_⟩
  dsimp only
  rw [hr]
  exact ⟨(roundedPower_bounds θ B).1, (roundedPower_bounds θ B).2, fun h => h ▸ roundedPower_zero B,
    roundedPower_error hθ B, hb⟩

end PowerRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
