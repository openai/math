import OAI.Hierarchy.ProbeBallPrices
import OAI.Hierarchy.ProbeBoxBound

namespace OAI
/-! # The same measured failure cutoff works for payload and post-purchase tests -/

namespace Hierarchy.AdaptiveProbe
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped BigOperators Classical
noncomputable section

/-- A value bound for both the exact physical role price and its bounded test
residual, independent of the input height, names and matching. -/
def wallCap (M box : ℝ) : ℝ := 2*M+box+abs ((⌈Real.sqrt 2*M⌉:ℤ):ℝ)+2

theorem printed_bounds {C H E A : Type*} {k : ℕ} {M box : ℝ} (hM : 0≤M) (hbox : 0≤box)
    (len : H→ℝ) (cost : ∀ e,0≤len e ∧ len e≤1) (y : A→ℝ) (quoted : ∀ a,0≤y a ∧ y a≤box)
    (r : ColumnWires.Role C H (A⊕E) k) :
    0 ≤ ColumnWires.quote M len (LocalCommodity.extraPrice y) r ∧
    ColumnWires.quote M len (LocalCommodity.extraPrice y) r ≤ wallCap M box := by
  have cap : 0≤abs ((⌈Real.sqrt 2*M⌉:ℤ):ℝ) := abs_nonneg _
  cases r with
  | catalyst => dsimp [ColumnWires.quote,wallCap]; constructor <;> linarith
  | radius => dsimp [ColumnWires.quote,wallCap]; constructor <;> linarith
  | cross =>
    dsimp [ColumnWires.quote,wallCap]
    constructor
    · positivity
    · linarith [le_abs_self ((⌈Real.sqrt 2*M⌉:ℤ):ℝ)]
  | horizontal e _ => dsimp [ColumnWires.quote,wallCap]; constructor <;> linarith [(cost e).1,(cost e).2]
  | extra e => cases e with
    | inl a => dsimp [ColumnWires.quote,LocalCommodity.extraPrice,wallCap]; constructor <;> linarith [(quoted a).1,(quoted a).2]
    | inr e => dsimp [ColumnWires.quote,LocalCommodity.extraPrice,wallCap]; constructor <;> linarith

/-- Both native gate errors are paid against the same public tolerance. The
small fractional purchase density may depend on W, but always precedes h,w. -/
def failureTolerance (N : ℕ) (ε ρ : ℝ) := min (ε/(10*(N+1))) (ε*ρ/20)

theorem failure_tolerance {N : ℕ} {ε ρ : ℝ} (he : 0<ε) (hd : 0<ρ) :
    let c := failureTolerance N ε ρ
    0<c ∧ ∀ n : ℕ, 5*c*n≤(n:ℝ)*ε/(2*(N+1)) ∧ 5*c*n≤ρ*n*ε/4 := by
  have denom : 0<10*((N:ℝ)+1) := by positivity
  have a := (le_div_iff₀ denom).1 (min_le_left (ε/(10*((N:ℝ)+1))) (ε*ρ/20))
  have b := min_le_right (ε/(10*((N:ℝ)+1))) (ε*ρ/20)
  refine ⟨lt_min (div_pos he denom) (by positivity),?_⟩
  intro n
  have nn : 0≤(n:ℝ) := Nat.cast_nonneg _
  constructor
  · apply (le_div_iff₀ (show 0<2*((N:ℝ)+1) by positivity)).2
    dsimp [failureTolerance]; nlinarith only [mul_le_mul_of_nonneg_right a nn]
  · dsimp [failureTolerance]; nlinarith only [mul_le_mul_of_nonneg_right b nn]

end
end Hierarchy.AdaptiveProbe

end OAI
