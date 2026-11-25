import OAI.Computability.BorderVNP.ShortenMeasuredRound
import OAI.Computability.BorderVNP.ShortenPreparedCatalog
import OAI.Computability.BorderVNP.ShortenCatalogProgram

/-!
# Preparing the physical stage before choosing the epoch fan-in

The common radius is fixed before any round. Each current finite catalog
then determines a finite frame table, relative bins, a depth floor and the
next site catalog. The same stage operates on arbitrary admissible children,
and every histogram branch returns a new admissible placed pack.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Crossing Epoch Cover Cover.Frame Framed Adaptive CombiningStep
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)

omit [Field K] in
private theorem PlacedStep.Measurements.withFits {P I U : Type} [Fintype I] [Fintype U]
    {bits : P → ℕ} {k d d' : ℕ} {child : Fin k → PlacedPack D P bits K I d}
    {s : PlacedStep m U d' child} {hk : 0 < k} {h h' ν ν' u v : ℝ}
    (M : PlacedStep.Measurements s hk h ν u v) (hh : h ≤ h') (hn : ν ≤ ν') :
    Nonempty (PlacedStep.Measurements s hk h' ν' u v) :=
  ⟨{M with fits := s.placed.fits_mono _ _ _ _ hh hn M.fits}⟩

/-- One actual stage at the prepared scale. The physical preservation of the
relative site list and radius holds for every possible joint histogram. -/
theorem PreparedBins.stageTemplate {S : Finset (HyperbolicHost (Cube D))} {h H ν θ η : ℝ}
    (B : PreparedBins D S h η) (hh : 0 ≤ h) (hH : h ≤ H) (hθ : θ ≤ ν)
    (hsafe : θ ≤ 4) (hη : η ≤ θ/4) : Nonempty (StageTemplate e (Cube D) h H ν S) := by
  obtain ⟨n,l,u,v,hu,hv,run⟩ := (B.eventually_measured (K := K) hh hη).exists
  refine ⟨{
    Bin := B.Bin
    nextSites := B.successorSites n e
    word := n
    floor := l
    meanFactor := u
    motionFactor := v
    nonneg := ⟨hu,hv⟩
    run := ?_
  }⟩
  intro d hd k hk P bits child prep
  obtain ⟨L,ω,g,hold,hchart,hproject,⟨measure⟩⟩ := run d hd (m := m) hk child
    (fun i => (prep i).sites) (fun i => (prep i).short) (fun i => (prep i).midpoint)
  let step := B.placedStep child L ω g
  refine ⟨step,measure.withFits hH hθ,?_⟩
  intro q
  obtain ⟨s,c⟩ := B.result_catalog child L ω g e (fun i => (prep i).sites) hold hchart hproject hsafe measure.fits q
  exact Catalog.PlacedAt.result e step q _ _ s c

/-- Fix one positive radius cap, at most one eighth, simultaneously for every
catalog that might arise in any later round. This leaves the radius needed for
final site rounding, while the quantitative saving still uses its original scale. -/
theorem exists_stageTemplates {H ν : ℝ} (hH : 0 < H) (hν : 0 < ν) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1/8 ∧ ∀ S : Finset (HyperbolicHost (Cube D)),
      Nonempty (StageTemplate e (Cube D) h H ν S) := by
  let θ := min ν 1
  have hθ : 0 < θ := lt_min hν zero_lt_one
  let η := θ/4
  have hη : 0 < η := div_pos hθ (by norm_num)
  obtain ⟨h₀,hp,charts⟩ := exists_preparedBins (D := D) hη
  let h := min (min H h₀) (1/8)
  have pos : 0 < h := lt_min (lt_min hH hp) (by norm_num)
  have hs : h ≤ min H h₀ := min_le_left ..
  refine ⟨h,pos,min_le_right ..,?_⟩
  intro S
  obtain ⟨B⟩ := charts h ⟨pos,hs.trans (min_le_right ..)⟩ S
  exact B.stageTemplate e pos.le (hs.trans (min_le_left ..)) (min_le_left ..)
    ((min_le_right ν (1:ℝ)).trans (by norm_num)) le_rfl

end Shortening

end BorderVNP
end Computability
end OAI
