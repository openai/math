import OAI.Computability.NearSquareRoot.PhysicalWalshFrontNamed
import OAI.Computability.NearSquareRoot.PhysicalWalshFrontSquareSelector
import OAI.Computability.NearSquareRoot.PhysicalWalshXorSquareClock

/-! # Uniform square-log dispatch for the native Walsh gate -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.FrontDispatch

open IntegerMultiplication Code PhysicalWalsh Space CommonRegisters GeneratorSyntax

/-- The branch reads the logarithm of the live descriptor size and compares
its square to the moving slot. -/
abbrev squareFits (a : ℕ) (s : Shape) := fitsReserve a (squareDegree (a+1) s) s

/-- The native gate already works at equality, so the elementary gate is
needed strictly below the threshold. -/
theorem squareCutoff (A : ℕ) (s : Shape) :
    XorThreshold.cutoff (squareDegree A s) (Header.scale A s) = (Nat.clog 2 (Header.scale A s + 1))^2 := by
  have nine : 9 ≤ Header.scale A s := by rw [Header.scale_exact]; omega
  have three : 2 < Nat.clog 2 (Header.scale A s + 1) := (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by omega)
  rw [XorThreshold.cutoff, Controlled.payloadBits, squareDegree, ←sq, max_eq_right]
  nlinarith

/-- Total extra scan charge at the runtime-computed reserve degree. -/
noncomputable def squareExtra (a W : ℕ) (ρ : ℝ) : Shape → ℕ :=
  branchClock a W ρ (squareDegree (a+1))

theorem squareExtra_bound (a W : ℕ) {ρ : ℝ} (half : 1/2 ≤ ρ) (upper : ρ ≤ 1) (s : Shape) :
    (squareExtra a W ρ s : ℝ) ≤ 5505*RouterClock.unit (a+1) ρ s := by
  unfold squareExtra branchClock FrontClock.extra
  rw [squareCutoff]
  split_ifs with short
  · exact (XorSquare.small_bound (a+1) half s short.le).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (zero_le_one.trans (RouterClock.one_le_unit ..)))
  · exact FrontClock.large_bound W (by linarith) upper s

/-- One effective file family chooses the native or the elementary gate by
the shape alone. The parameter used to generate the two branch programs
may include arbitrary kernel or interpreter tables. -/
theorem compileSquareGate {Z : Type} [Primcodable Z] (a : Z → ℕ) (ha : Computable a)
    (small large : Z → Cmd) (es : Effective ltr small) (el : Effective ltr large) (R : ℕ)
    (regS : ∀ z, Within R (small z)) (regL : ∀ z, Within R (large z)) :
    ∃ (emit : Z → Cmd) (N e : ℕ), Effective ltr emit ∧ 0 < N ∧ (∀ z, Within N (emit z)) ∧
      ∀ (z : Z) (W : ℕ) (ρ : ℝ) (arity : 4 ≤ a z) (d : ℕ), e ≤ d →
        let A := a z+1
        let g := Interior.axes (a z) arity
        branchRuns (W:=W) g (fun s => ¬ squareFits (a z) s)
          (nodeScan (a z) W d (ElementarySweep.extra A)) (nodeArena (a z) W d) (small z) →
        branchRuns (W:=W) g (squareFits (a z))
          (fun s => allowance A d s + Interior.extra (a z) W ρ s) (allowance A d) (large z) →
        PhysicalWalshCompileXorPacket.FlatRuns (W:=W)
          (nodeScan (a z) W d (squareExtra (a z) W ρ)) (nodeArena (a z) W d) g (emit z) := by
  obtain ⟨tag,K,e,et,rt,ht⟩ := compileSquareSelector
  obtain ⟨emit,N,ee,pN,reg,run⟩ :=
    compileGateWith a (fun z => squareDegree (a z+1)) (tag ∘ a) K e (et.comp ha) (fun z => rt _)
      (fun z W d => ht (a z) W d) small large es el R regS regL
  exact ⟨emit,N,e,ee,pN,reg,run⟩

end PhysicalWalshNode.FrontDispatch

end NearSquareRoot
end Computability
end OAI
