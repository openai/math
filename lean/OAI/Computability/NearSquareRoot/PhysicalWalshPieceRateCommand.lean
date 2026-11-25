import OAI.Computability.NearSquareRoot.PhysicalWalshPieceBudget
import OAI.Computability.NearSquareRoot.PhysicalWalshRoundedCommand

/-! # Closed piece rates for the generated sweep command -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces

open IntegerMultiplication Code Space PhysicalWalshNode KernelPass

/-- The named sweep runs the supplied piece command on the sequentially
reached records, charging each level with its exact schedule multiplicity. -/
theorem roundedSweepRateNamed {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W) (piece : Cmd)
    {ρ B c : ℝ} {L P : ℕ → ℝ} (hP : ∀ w, 0 ≤ P w)
    (raw : EffectiveBoundedTask.Runs piece
      (fun v : Admitted hw p => pieceTimeBound (a+1) p.calls ρ B L P v.val.shape)
      (fun v => pieceSpaceBound (a+1) c P v.val.shape) (rawInput hw p) (rawOutput hw p))
    {I : Type} (ha : 1 < a+1) (b : I → Root)
    (capacity : ∀ i, (b i).size (a:=a) (W:=W) ≤ 2^((b i).w+1))
    (fits : ∀ i, (b i).Feasible hw p ha) :
    ∃ d C : ℕ, EffectiveBoundedTask.Runs (sweepCmd (a+1) W piece)
      (fun i => sweepTime (a+1) W p.calls ρ B c L P C d (b i).k (b i).s (b i).w)
      (fun i => sweepSpace (a+1) W c P C d (b i).k (b i).s (b i).w)
      (fun i => input (a:=a) (W:=W) (b i)) (fun i => output hw p (b i)) := by
  apply roundedSweepNamed hw p piece ha b capacity fits
    (pieceTimeBound (a+1) p.calls ρ B L P) (pieceSpaceBound (a+1) c P) raw
    (fun i => stageClock (a+1) W p.calls ρ B L P (b i).k (b i).s (b i).w)
    (fun i => sweepArena (a+1) W c P (b i).k (b i).s (b i).w)
  · exact fun i j => (stageClock_at hw ha (b i) j p.calls ρ B L P).le
  · exact fun i j => sweepArena_at hw ha (b i) j c P hP
  · exact fun _ => le_max_left ..

end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
