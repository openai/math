import OAI.Computability.NearSquareRoot.PhysicalWalshSparseSweep
import OAI.Computability.NearSquareRoot.PhysicalWalshPieceRateCommand

/-! # Uniform sparse bounds on the generated Walsh sweep command -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces

open IntegerMultiplication Code PhysicalWalshNode KernelPass

/-- The compact-header agenda interpreter runs the supplied piece command,
including all repeated stages, within the sparse time and space bounds. -/
theorem sparseRoundedSweepNamed {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W) (piece : Cmd)
    (ha : 1 < a+1)
    {ρ B c : ℝ} {L P : ℕ → ℝ} (hr : 0 < ρ) (hB : 0 ≤ B) (hc : 0 ≤ c) (hP : ∀ w, 0 ≤ P w)
    (raw : EffectiveBoundedTask.Runs piece
      (fun v : Admitted hw p => pieceTimeBound (a+1) p.calls ρ B L P v.val.shape)
      (fun v => pieceSpaceBound (a+1) c P v.val.shape) (rawInput hw p) (rawOutput hw p))
    {I : Type} (b : I → Root)
    (capacity : ∀ i, (b i).size (a:=a) (W:=W) ≤ 2^((b i).w+1)) (fits : ∀ i, (b i).Feasible hw p ha)
    {g R H Q : ℝ} {q : ℕ} (hg : 0 < g) (hR : 0 ≤ R) (hH : 0 ≤ H) (hQ : 0 ≤ Q)
    (sparse : ∀ i, ((b i).s:ℝ) ≤ g*(b i).k/Real.log (2+(b i).k))
    (width : ∀ i, ((b i).w:ℝ) ≤ R*((b i).k+1))
    (overhead : ∀ i, 0 ≤ L (b i).w ∧ L (b i).w ≤ H*(1+Real.log (2+(b i).k)))
    (setup : ∀ i, P (b i).w ≤ Q*((b i).k+1:ℝ)^q) :
    EffectiveBoundedTask.Runs (sweepCmd (a+1) W piece)
      (fun i => sparseTime ρ (b i).k) (fun i => sparseSpace (b i).k)
      (fun i => input (a:=a) (W:=W) (b i)) (fun i => output hw p (b i)) := by
  obtain ⟨d,C,run⟩ := roundedSweepRateNamed hw p piece hP raw ha b capacity fits
  obtain ⟨M,N,tm,sp⟩ := sparseClock_bounds (calls:=p.calls) (C:=C) (d:=d) ha hw hr hB hc hP b
    hg hR hH hQ sparse width overhead setup
  exact run.bound M N tm sp

end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
