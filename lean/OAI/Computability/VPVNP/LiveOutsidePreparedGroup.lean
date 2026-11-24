import OAI.Computability.VPVNP.LiveOutsidePreparedPair
import OAI.Computability.VPVNP.LiveOutsideGroupTraces

/-!
# Charging the prepared first-half branch at the actual native cap

The auxiliary preparation supplies the two indexed stages and the input
memory facts used to bound their native logs. The only separately charged
work is the compressed pair simulation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.OutsideTraces

open BurstRAM BurstRAM.PrivateRAM PairStages.Group PairStages.Group.Auxiliary
open LiveAuxiliaryHeaders PrimedInputRAM

variable (G : PairStages.Group) (i : Fin (2^(Auxiliary.sizes G).h))
variable (F : Nominations.Fits G) (m : Memory G.w) (tag : G.tagged Stage.nominations m)
variable (hdr : Header (pairLengths G i) → Bool)
variable (B : ∀ μ, PreparedBranch G m i hdr (Nominations.indexed G F m tag) μ)
variable {Path : Nominations.Nom G → Type*}
variable (pair : ∀ μ, Indexed G Stage.pair ((B μ).copy.memory ()) (Path μ))

/-- The native chronology induced by the actually prepared auxiliary input
and the indexed compressed computation. -/
noncomputable def preparedChronology : Chronology G m (Nominations.Nom G) Path :=
  ⟨Nominations.indexed G F m tag,fun μ => (B μ).init,fun μ => (B μ).copy,pair⟩

/-- A direct bound on all non-compression reports of an accepted first-half
path. No separate clock or probe estimates for the three preparation stages
are required. -/
theorem prepared_outside (header : List (Report G.w))
    (hr : Resources header (LiveHeaderSchedule.costBound (OutsideTraces.sizes G)) 11 154)
    (fit : shadowBase G+span (pairLengths G i) (histLength G) ≤ 2^G.w)
    (clock : 68 ≤ G.clockAt Stage.auxiliaryCopy) (μ : Nominations.Nom G) (q : Path μ)
    (raw : ℕ) (first last empty : Bool) :
    Resources (outsidePair (preparedChronology G i F m tag hdr B pair) header μ q)
      (OutsideBudget.actualBound G.constants G.g raw first last empty)
      26 (max 154 (5*(2*G.g.d)+23)) := by
  obtain ⟨hn,hi,hc⟩ := OutsideBudget.prepared_resources G i F m tag μ (B μ) fit clock
  exact pair_outside_resources (preparedChronology G i F m tag hdr B pair) header μ q hr hn hi hc raw first last empty

/-- The report-cap premise of `Chronology.count` on the prepared pair.
An accepted compressed computation consumes the remaining bucket capacity. -/
theorem prepared_enough (header : List (Report G.w))
    (hr : Resources header (LiveHeaderSchedule.costBound (OutsideTraces.sizes G)) 11 154)
    (fit : shadowBase G+span (pairLengths G i) (histLength G) ≤ 2^G.w)
    (clock : 68 ≤ G.clockAt Stage.auxiliaryCopy) (μ : Nominations.Nom G) (q : Path μ)
    (raw S H : ℕ) (first last empty : Bool)
    (hout : OutsideBudget.actualBound G.constants G.g raw first last empty ≤ S) (hH : 26 ≤ H)
    (pairCost : RAMBuckets.cost Report.probes ((pair μ).logs q) ≤ S*(H-1))
    (pairCalls : ∀ r ∈ (pair μ).logs q, 1+r.probes ≤ H) :
    let A := preparedChronology G i F m tag hdr B pair
    withinCaps S H ((header++[modePairReport G]) ++ (A.prefixLogs μ q ++ exponentLogs A μ q)) := by
  have outside := prepared_outside G i F m tag hdr B pair header hr fit clock μ q raw first last empty
  exact pair_withinCaps (preparedChronology G i F m tag hdr B pair) header μ q outside hout hH pairCost pairCalls

end LiveProgram.OutsideTraces

end VPVNP
end Computability
end OAI
