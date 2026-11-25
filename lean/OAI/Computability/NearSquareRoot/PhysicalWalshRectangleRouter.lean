import OAI.Computability.NearSquareRoot.CRTPositionRouterTotal
import OAI.Computability.NearSquareRoot.PhysicalWalshPositionCommand
import OAI.Computability.NearSquareRoot.PhysicalWalshGatherTotal

/-! # Routing the original Walsh record array with a named rectangular interchanger -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.GatherProgram

open IntegerMultiplication Code FixedPoint Controlled Adic Strip
open CommonRegisters GeneratorSyntax

noncomputable section

/-- The same compact position program gathers and restores an arbitrary supplied bit mask.
Its small-width branch and both reserve coefficients are part of the emitted command. -/
def rectangleRouter (low high : ℕ) (rectangle : Cmd) : Cmd :=
  positionCmd (PositionProgram.routeCmd low high rectangle)

theorem rectangleRouter_effective {J : Type} [Primcodable J] {low high : J → ℕ}
    {rectangle : J → Cmd} (hl : Computable low) (hh : Computable high)
    (hr : GeneratorSyntax.Effective ltr rectangle) :
    GeneratorSyntax.Effective ltr (fun j => rectangleRouter (low j) (high j) (rectangle j)) :=
  positionCmd_effective (PositionProgram.routeCmd_effective hl hh hr)

theorem rectangleRouter_within (R : ℕ) :
    ∃ S, 0 < S ∧ ∀ a b c, Within R c → Within S (rectangleRouter a b c) := by
  obtain ⟨T,_,hn⟩ := PositionProgram.routeCmd_within R
  obtain ⟨S,hS,hw⟩ := positionCmd_within T
  exact ⟨S,hS,fun a b c hc => hw _ (hn a b c hc)⟩

/-- An unrestricted finite run on every native table and pair of component films
is enough to execute the same outer source on the original marked record lists. -/
theorem positionTotalAt_of_native {native : Cmd} {K : ℕ}
    (runs : ∃ t : NativeInput K → ℕ, EffectiveTask.Runs native t
      (fun q => .fork (send (Reflections.table q.val.positions))
        (PositionCloth.nativeRows (fun z : NativeInput K => z.val.k)
          (fun z i => z.val.row (flatAddress 2 z.val.k i)) q))
      (PositionCloth.nativeRows (fun q : NativeInput K => q.val.k)
        (fun q i => q.val.row (flatAddress 2 q.val.k (flatBitPullback q.val.positions i))))) :
    PositionTotalAt (positionCmd native) K := by
  obtain ⟨t,run⟩ := runs
  have nativeRun : NativeAt native t _ (fun q => flatBitPullback q.val.positions) :=
    EffectiveBoundedTask.Runs.of_time run
  exact ⟨_,_,positionCmd_runs nativeRun⟩

/-- All reserve guesses correctly permute the complete Walsh record stream. -/
theorem rectangleRouter_total {rect : Cmd} {ρ : ℝ} (rate : 0 ≤ ρ)
    (rectangle : Controlled.Effective.rectContract rect ρ) (a b : ℕ) :
    PositionTotalAt (rectangleRouter a b rect) 0 := by
  apply positionTotalAt_of_native
  let k (q : NativeInput 0) := q.val.k
  let u (q : NativeInput 0) := Series.natural (2*(componentBits (k q)+1))
  let p (q : NativeInput 0) := q.val.positions
  let f (q : NativeInput 0) (z : Block 2 (k q)) := Dusk.stock (q.val.row (flatAddress 2 (k q) z))
  exact PositionProgram.routeCmd_total rate rectangle a b k u
    (fun q => by simp only [u,Series.count_natural]; omega) p f

/-- Rectangular interchange gives the sharp router on every address width, including zero,
once the two literal reserve degrees exceed a bound independent of the data and the mask. -/
theorem rectangleRouter_runs {rect : Cmd} {ρ : ℝ} (rate : 0 ≤ ρ)
    (rectangle : Controlled.Effective.rectContract rect ρ) :
    ∃ D : ℕ, ∀ a b, D ≤ a → D ≤ b → PositionRunsAt (rectangleRouter a b rect) ρ 0 := by
  obtain ⟨D,run⟩ := PositionProgram.routeCmd_runs rate rectangle
  refine ⟨max D (⌈ρ⌉₊+2),fun a b ha hb => ?_⟩
  apply positionRunsAt_of_native rate
  let k (q : NativeInput 0) := q.val.k
  let u (q : NativeInput 0) := Series.natural (2*(componentBits (k q)+1))
  let p (q : NativeInput 0) := q.val.positions
  let f (q : NativeInput 0) (z : Block 2 (k q)) := Dusk.stock (q.val.row (flatAddress 2 (k q) z))
  have runs := run a b ((le_max_left ..).trans ha) ((le_max_left ..).trans hb) ((le_max_right ..).trans hb)
    k u (fun q => by simp only [u,Series.count_natural]; omega) p f
  simpa only [NativePositionAt,NativeAt,nativeVolume,PositionCloth.nativeRows,DigitPacking.recordCloth,
    PositionCmd.PositionRuns, u, p, f, k, Series.count_natural] using runs

end
end PhysicalWalsh.GatherProgram

end NearSquareRoot
end Computability
end OAI
