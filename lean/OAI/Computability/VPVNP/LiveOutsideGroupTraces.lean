import OAI.Computability.VPVNP.LiveOutsidePairStages
import OAI.Computability.VPVNP.LiveOutsideTailStages
import OAI.Computability.VPVNP.LiveProgramPairCount

/-!
# Resource caps for the physical unit and paired group traces

The pair chronology places the compressed computation between the
auxiliary-input copy and the exponent check. Its cost is charged separately.
All other reports in the same path are charged to the public polynomial
bound from Section 14.2.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.OutsideTraces

open BurstRAM BurstRAM.PrivateRAM LiveHeaderSchedule OutsideBudget

variable (G : PairStages.Group)

/-- The linked mode-router report selecting the paired branch and entering nominations. -/
def modePairReport := Router.mode.outerReport G.evaluator G.g G.lit
  (Router.mode.jumpReport G.g G.lit 1 1 LiveProgram.Stage.nominations)

/-- The linked mode-router report selecting the evaluator branch and entering the first-tail
router. -/
def modeTailReport := Router.mode.outerReport G.evaluator G.g G.lit
  (Router.mode.jumpReport G.g G.lit 2 2 LiveProgram.Stage.firstTail)

/-- The live-header dimensions used to charge this physical group's outside reports. -/
abbrev sizes := G.constants.lengths.eval G.g
/-- The number of labels in the live exponent check at this group's geometry. -/
abbrev labels := G.constants.labels.eval G.g
/-- The number of binary exponent digits per label at this group's geometry. -/
abbrev rowWidth := G.constants.Z.eval G.g

/-- Unit mode consists of the recovered headers and one accepting mode router call. -/
theorem unit_resources (header : List (Report G.w)) (hr : Resources header (costBound (sizes G)) 11 154)
    (raw : ℕ) (first last empty : Bool) :
    Resources (header++[UnitGroup.report G]) (actualBound G.constants G.g raw first last empty) 11 154 := by
  have rt := router_halt Router.mode G.evaluator G.g G.lit 0 0
  have sum := hr.append rt
  refine ⟨sum.cost.trans ?_,sum.calls,sum.work⟩
  dsimp only [actualBound,sizes]
  omega

variable {G} {m : Memory G.w} {Nom : Type*} {Path : Nom → Type*}
variable (A : PairStages.Group.Chronology G m Nom Path)

/-- The linked exponent-check reports starting on the memory returned by the selected native
pair path. -/
noncomputable def exponentLogs (μ : Nom) (q : Path μ) :=
  (LiveExponent.stageReports G.exponentPub (labels G) (rowWidth G) ((A.pair μ).memory q)).map
    (LiveStageLink.linkedReport G.nextStage G.addr LiveProgram.Stage.exponents)

/-- Precisely the reports outside the compressed pair subroutine. -/
noncomputable def outsidePair (header : List (Report G.w)) (μ : Nom) (q : Path μ) :=
  (header ++ [modePairReport G]) ++ (A.nominations.logs μ ++ ((A.init μ).logs () ++
    ((A.copy μ).logs () ++ exponentLogs A μ q)))

/-- Full paired branch in the same order as the actual native path bijection. -/
noncomputable def wholePair (header : List (Report G.w)) (μ : Nom) (q : Path μ) :=
  (header ++ [modePairReport G]) ++ (A.prefixLogs μ q ++ exponentLogs A μ q)

theorem pair_cost_identity (header : List (Report G.w)) (μ : Nom) (q : Path μ) :
    RAMBuckets.cost Report.probes (wholePair A header μ q) =
      RAMBuckets.cost Report.probes (outsidePair A header μ q) + RAMBuckets.cost Report.probes ((A.pair μ).logs q) := by
  simp only [wholePair,outsidePair,PairStages.Group.Chronology.prefixLogs,RAMBuckets.cost_append]
  omega

private theorem member_pair {header : List (Report G.w)} {μ : Nom} {q : Path μ} {r : Report G.w}
    (h : r ∈ wholePair A header μ q) : r ∈ outsidePair A header μ q ∨ r ∈ (A.pair μ).logs q := by
  simp only [wholePair,outsidePair,PairStages.Group.Chronology.prefixLogs,List.mem_append] at *
  tauto

/-- The exact measured preparation stages, with the compiled exponent sweep
on the memory passed out by the compressed computation. The three source
stage bounds are furnished by the native nomination, initialization and
copy theorems in `LiveOutsidePairStages`. -/
theorem pair_outside_resources (header : List (Report G.w)) (μ : Nom) (q : Path μ)
    (hr : Resources header (costBound (sizes G)) 11 154)
    (hn : Resources (A.nominations.logs μ) (4*(labels G+1)) 3 (5*(2*G.g.d)+23))
    (hi : Resources ((A.init μ).logs ()) 100 26 92)
    (hc : Resources ((A.copy μ).logs ()) (16*(auxWords (sizes G) (labels G)+1)) 15 115)
    (raw : ℕ) (first last empty : Bool) :
    Resources (outsidePair A header μ q) (actualBound G.constants G.g raw first last empty)
      26 (max 154 (5*(2*G.g.d)+23)) := by
  have route := router_jump Router.mode G.evaluator G.g G.lit 1 1 LiveProgram.Stage.nominations
  have exp := exponent_resources G (labels G) (rowWidth G) ((A.pair μ).memory q)
  have sum := (hr.append route).append (hn.append (hi.append (hc.append exp)))
  refine ⟨sum.cost.trans ?_,fun r h => (sum.calls r h).trans ?_,fun r h => (sum.work r h).trans ?_⟩
  · dsimp only [actualBound,sizes,labels,rowWidth]
    omega
  · decide
  · omega

/-- The outside trace fits one processor array. The remaining bucket capacity
covers the compressed subroutine. The per-call check follows the report
membership on the very same chronological path. -/
theorem pair_withinCaps (header : List (Report G.w)) (μ : Nom) (q : Path μ)
    {cost work S H : ℕ} (outside : Resources (outsidePair A header μ q) cost 26 work)
    (hout : cost ≤ S) (hH : 26 ≤ H)
    (pairCost : RAMBuckets.cost Report.probes ((A.pair μ).logs q) ≤ S*(H-1))
    (pairCalls : ∀ r ∈ (A.pair μ).logs q, 1+r.probes ≤ H) : withinCaps S H (wholePair A header μ q) := by
  constructor
  · rw [pair_cost_identity]
    calc
      _ ≤ S + S*(H-1) := Nat.add_le_add (outside.cost.trans hout) pairCost
      _ = S*H := by rw [Nat.add_comm S,← Nat.mul_succ,show (H-1).succ=H by omega]
  · intro r hr
    exact (member_pair A hr).elim (fun h => (outside.calls r h).trans hH) (pairCalls r)

/-- A uniform clock for the private instructions of the complete paired group. -/
theorem pair_private (header : List (Report G.w)) (μ : Nom) (q : Path μ)
    {cost work clock : ℕ} (outside : Resources (outsidePair A header μ q) cost 26 work)
    (hout : work ≤ clock) (pairWork : ∀ r ∈ (A.pair μ).logs q, r.events.length+1 ≤ clock) :
    ∀ r ∈ wholePair A header μ q, r.events.length+1 ≤ clock := by
  intro r hr
  exact (member_pair A hr).elim (fun h => (outside.work r h).trans hout) (pairWork r)

/-- The full evaluator branch, including the common header, the mode jump,
both boundary routers, the selected setup and gather stages, and the
actual terminal evaluator burst. -/
theorem tail_group_resources (G : PairStages.Group) (header : List (Report G.w))
    (hr : Resources header (costBound (sizes G)) 11 154)
    (raw : List Bool) {first last : Bool} {xs ys : List (Report G.w)}
    (incoming : OutsideTailStages.Incoming G raw first xs) (outgoing : OutsideTailStages.Outgoing G raw last ys)
    (hl : LiveEvaluatorRAM.PrepLayout G.evaluator G.transitionPub (OutsideTailStages.params G raw.length).radius)
    (mem : Memory G.w) (bits : List (List Bool)) (rs : List (Report G.w)) {f : ℕ}
    (run : runSegment (LiveEvaluatorRAM.Schedule.nativeProgram G.evaluator G.transitionPub) f (some 0) mem bits = some rs)
    (halt : endState (some 0) rs = none) :
    Resources ((header++[modeTailReport G]) ++ (xs++ys++G.linkedLogs LiveProgram.Stage.transition rs))
      (actualBound G.constants G.g raw.length first last (decide (G.evaluator.extra=0)))
      (OutsideTailStages.callBound G.w) (max 154 (OutsideTailStages.instructionBound G)) := by
  have route := router_jump Router.mode G.evaluator G.g G.lit 2 2 LiveProgram.Stage.firstTail
  have tail := OutsideTailStages.tail_resources G raw incoming outgoing hl mem bits rs run halt
  have bound := (hr.append route).append tail
  refine ⟨bound.cost.trans ?_,fun r h => (bound.calls r h).trans ?_,fun r h => (bound.work r h).trans ?_⟩
  · dsimp only [actualBound,OutsideTailStages.params,sizes,PairStages.Group.w]
    omega
  · unfold OutsideTailStages.callBound
    omega
  · omega

/-- A complete outside-only route uses at most one processor array. Its
per-call resource estimate gives the other half of the transcript cap. -/
theorem outside_only_cap {w : ℕ} {rs : List (Report w)} {cost per work S H : ℕ}
    (resource : Resources rs cost per work) (hc : cost ≤ S) (hH : 0 < H) (hp : per ≤ H) :
    withinCaps S H rs := resource.cap (hc.trans (Nat.le_mul_of_pos_right _ hH)) hp

theorem unit_group_cap (G : PairStages.Group) (header : List (Report G.w))
    (hr : Resources header (costBound (sizes G)) 11 154) (raw S H : ℕ) (first last empty : Bool)
    (hc : actualBound G.constants G.g raw first last empty ≤ S) (hH : 11 ≤ H) :
    withinCaps S H (header++[UnitGroup.report G]) :=
  outside_only_cap (unit_resources G header hr raw first last empty) hc (by omega) hH

theorem tail_group_cap (G : PairStages.Group) (header : List (Report G.w))
    (hr : Resources header (costBound (sizes G)) 11 154)
    (raw : List Bool) {first last : Bool} {xs ys : List (Report G.w)}
    (incoming : OutsideTailStages.Incoming G raw first xs) (outgoing : OutsideTailStages.Outgoing G raw last ys)
    (hl : LiveEvaluatorRAM.PrepLayout G.evaluator G.transitionPub (OutsideTailStages.params G raw.length).radius)
    (mem : Memory G.w) (bits : List (List Bool)) (rs : List (Report G.w)) {f S H : ℕ}
    (run : runSegment (LiveEvaluatorRAM.Schedule.nativeProgram G.evaluator G.transitionPub) f (some 0) mem bits = some rs)
    (halt : endState (some 0) rs = none)
    (hc : actualBound G.constants G.g raw.length first last (decide (G.evaluator.extra=0)) ≤ S)
    (hH : OutsideTailStages.callBound G.w ≤ H) :
    withinCaps S H ((header++[modeTailReport G]) ++ (xs++ys++G.linkedLogs LiveProgram.Stage.transition rs)) := by
  have hpos : 0 < H := by unfold OutsideTailStages.callBound at hH; omega
  exact outside_only_cap (tail_group_resources G header hr raw incoming outgoing hl mem bits rs run halt) hc hpos hH

/-- The same choice of B works for every valid trace, every route, and
every actual advice prefix up to the public capacity. -/
theorem eventually_below_R (c : Constants) :
    ∃ B₀ : ℕ, ∀ B ≥ B₀, ∀ᶠ n : ℕ in Filter.atTop, ∀ H raw first last empty,
      let g := paperGeometry B (fun _ => H) n
      ∀ (rs : List (Report g.w)) (per work : ℕ), raw ≤ c.prefixCapacity.eval g →
        Resources rs (actualBound c g raw first last empty) per work →
        RAMBuckets.cost Report.probes rs < CursorBounds.processorCount B n := by
  obtain ⟨B₀,h⟩ := eventually_actual c
  refine ⟨B₀,fun B hB => ?_⟩
  filter_upwards [h B hB] with n hn
  intro H raw first last empty
  dsimp only
  intro rs per work hraw res
  exact res.cost.trans_lt (hn H raw first last empty hraw)

end LiveProgram.OutsideTraces

end VPVNP
end Computability
end OAI
