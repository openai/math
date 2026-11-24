import OAI.Computability.VPVNP.CompressorShrinkBundlePlan
import OAI.Computability.VPVNP.CompressorShrinkSlotPlan
import OAI.Computability.VPVNP.CompressorSourceWalk

/-!
# Native sources for dense shrinking visits

Each stage indexes its worker in the block planner. The first ten stages
replay the placement, rank and width reports from the physical shrinking
run, starting in the memory left by the two greedy assignments.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkBundlePlan.Scheduled

open BurstRAM BurstRAM.PrivateRAM Compression PhaseRecipe BlockPlanner
open scoped Fin.CommRing

/-- The eleven dense bundle worker stages, from preliminary placement and rank preparation to
AB pieces and absolute identifiers. -/
inductive Stage where
  | positions | clear | classify | collect | gather | rank | scatter
  | thickPrefix | motifPrefix | ab | absolute
  deriving DecidableEq

/-- Number a bundle stage from zero for placement to ten for the final absolute-ID pass. -/
def Stage.index : Stage → Fin 11
  | .positions => 0
  | .clear => 1
  | .classify => 2
  | .collect => 3
  | .gather => 4
  | .rank => 5
  | .scatter => 6
  | .thickPrefix => 7
  | .motifPrefix => 8
  | .ab => 9
  | .absolute => 10

/-- The first ten bundle stages that prepare the sorted widths, both prefix tables and AB
pieces. -/
def preparationOrder : List Stage :=
  [.positions,.clear,.classify,.collect,.gather,.rank,.scatter,.thickPrefix,.motifPrefix,.ab]

/-- The full bundle-stage sequence, ending with the absolute-ID scan after preparation. -/
def order := preparationOrder ++ [.absolute]

variable (shape : DescriptorSpace.Shape) (step a : ℕ) (origin : Expr)

/-- Select the planned catalog visit corresponding to a bundle stage at the specified level and
arena. -/
def Stage.visit (j : Stage) : Visit :=
  (visits shape step a origin)[j.index.val]'(by rw [visits_length]; exact j.index.isLt)

theorem order_visits : order.map (Stage.visit shape step a origin) = visits shape step a origin := rfl

/-- Number of public operands required by the local worker for this bundle stage. -/
abbrev Stage.arity : Stage → ℕ
  | .positions => 14
  | .clear => 1
  | .classify => 11
  | .collect | .rank => 6
  | .gather | .absolute => 7
  | .scatter | .thickPrefix | .motifPrefix | .ab => 5

theorem Stage.params (j : Stage) : (j.visit shape step a origin).worker.params = j.arity := by
  cases j <;> rfl

variable {a} {w g : ℕ} (X : State a (packingLaneBits a g)) (T : IncidenceDirectory w) (start : ℕ)

local notation "Z" => ShrinkInput.plan X start
local notation "q" => ShrinkRankSpace.Shape.collectBank (ShrinkInput.plan X start) w
local notation "sh" => ShrinkInput.placementBank X T start
local notation "rankWord" => (Fin.ofNat (2^w) (ShrinkRankSpace.Shape.ranks (ShrinkInput.plan X start)))
local notation "W" => ShrinkInput.widthBase X start

/-- Exclusive cursor bound for the stage, determined by its scan over sites, ports, bucket
counts or bundle fields. -/
def Stage.limit : Stage → ℕ
  | .positions => Fintype.card X.Base * 2^(packingLaneBits a g)
  | .clear => 2*(Z).B
  | .classify | .collect | .gather | .rank | .scatter | .absolute => (Z).A
  | .thickPrefix => (Z).B * thickCount a
  | .motifPrefix | .ab => (Z).B * (Z).Q

/-- The stage-specific public operand words assembled from the input incidence directory,
preliminary placement and rank and width arenas. -/
def Stage.bank : (j : Stage) → Fin j.arity → Word w
  | .positions => sh
  | .clear => fun _ ↦ q 3
  | .classify => (Z).classifyBank T sh
  | .collect => q
  | .gather => BundleGather.Fixed.parameters ((Z).gatheredTable w T)
  | .rank => BundleGather.rankPublic q (Fin.ofNat _ (Z).key) (Fin.ofNat _ (Z).gathered) rankWord
  | .scatter => ShrinkWidthArena.scatterBank T q rankWord W
  | .thickPrefix => ShrinkWidthArena.prefixBank X T q rankWord W false
  | .motifPrefix => ShrinkWidthArena.prefixBank X T q rankWord W true
  | .ab => ShrinkWidthArena.abBank X T q rankWord W
  | .absolute => absoluteBank Z w

section Readback

variable {shape step origin start T} {pub : Fin 5 → Word w} {state : Word w} {m : Memory w}
  (h : Reads X shape step origin pub state m start T)

include h in
theorem Stage.stop (j : Stage) :
    (j.visit shape step a origin).stop.eval pub state m = (j.limit X start : Word w) := by
  have e := congrArg (fun l : List (Word w) ↦ l[j.index.val]?) (stop_counts X h)
  cases j <;> exact Option.some.inj e

include h in
theorem Stage.operands (j : Stage) (fit : (Z).stop < 2^w) :
    (fun i ↦ ((j.visit shape step a origin).params i).eval pub state m) =
      j.bank X T start ∘ Fin.cast (j.params shape step a origin) := by
  obtain ⟨hc,hl,hg,hr,hw⟩ := rank_banks X h fit
  cases j with
  | positions => exact placement_bank X h
  | clear => funext i; exact (head_values X h).counts
  | classify => exact hc
  | collect => exact hl
  | gather => exact hg
  | rank => exact hr
  | scatter => exact hw
  | thickPrefix => exact prefix_bank X h false fit
  | motifPrefix => exact prefix_bank X h true fit
  | ab => exact ab_bank X h fit
  | absolute => exact absolute_bank X h

include h in
theorem Stage.words (j : Stage) (fit : (Z).stop < 2^w) (tag : Word w) :
    ShrinkSlotPlan.words (j.visit shape step a origin) tag pub state m =
      tag :: 0 :: (j.limit X start : Word w) :: List.ofFn (j.bank X T start) := by
  rw [ShrinkSlotPlan.words,j.stop X h,j.operands X h fit]
  cases j <;> rfl

end Readback

/-- The checked segment for a worker from the planner, with its physical bank
and one empty choice tape per cursor value. -/
def Source (X : State a (packingLaneBits a g)) (T : IncidenceDirectory w) (start : ℕ)
    (shape : DescriptorSpace.Shape) (step : ℕ) (origin : Expr) (j : Stage)
    (mem : Memory w) (rs : List (Report w)) : Prop :=
  let v := j.visit shape step a origin
  let bank := j.bank X T start ∘ Fin.cast (j.params shape step a origin)
  runSegment (v.worker.table.instantiate w bank).program (v.worker.pcs-1) (some 0) mem
    (List.replicate (j.limit X start) []) = some rs

variable {m : Memory w}

/-- Concatenate the physical reports of the first ten preparation scans in their execution
order through AB piece construction. -/
def preparationReports (r : ShrinkInput.Run X T start m) : List (Report w) :=
  r.sites ++ r.clear ++ r.classify ++ r.append ++ r.gather ++ r.rank ++
    r.scatter ++ r.thickPrefixes ++ r.cdPrefixes ++ r.abPieces

theorem preparation_post (r : ShrinkInput.Run X T start m) :
    after r.greedy.post (eventLog (preparationReports X T start r)) = r.post := by
  simp only [preparationReports,SourceWalk.after_append]
  rfl

/-- All ten deterministic report lists in their native chronological order. -/
theorem preparation_sources (r : ShrinkInput.Run X T start m) (fit : (Z).stop < 2^w) :
    SourceWalk (Source X T start shape step origin) preparationOrder r.greedy.post (preparationReports X T start r) := by
  classical
  have hQ := ((Z).scalarFits Fintype.card_pos fit).2.2.1
  have ht : thickCount a ≤ (Z).Q := by
    change 2^(Shrink.colors a)*2^a/4 ≤ 3*(2^(Shrink.colors a)*2^a)/4
    omega
  have thick := r.widths.prefixes.thick.executed
  have motif := r.widths.prefixes.motif.executed
  have thickSize : (ShrinkWidthArena.prefixBank X T q rankWord W false 0).val = thickCount a :=
    Nat.mod_eq_of_lt (ht.trans_lt hQ)
  have motifSize : (ShrinkWidthArena.prefixBank X T q rankWord W true 0).val = (Z).Q :=
    Nat.mod_eq_of_lt hQ
  rw [thickSize] at thick
  rw [motifSize] at motif
  have ranked := r.ranking.ranked.rank.executed
  rw [Nat.add_comm 1] at ranked
  simp only [preparationOrder,preparationReports,List.append_assoc]
  exact .next r.positions (.next r.ranking.clear (.next r.ranking.ranked.classify
    (.next r.ranking.ranked.append (.next r.ranking.ranked.gather (.next ranked
    (.next r.widths.scatter (.next thick (.next motif (.singleton r.widths.ab)))))))))

theorem source_paths {j : Stage} {rs : List (Report w)}
    (run : Source X T start shape step origin j m rs) :
    branchPaths rs = List.replicate (j.limit X start) [] :=
  ((runSegment_iff ..).mp run).2.2

theorem source_calls {j : Stage} {rs : List (Report w)}
    (run : Source X T start shape step origin j m rs) : rs.length = j.limit X start := by
  simpa [branchPaths] using congrArg List.length (source_paths shape step origin X T start run)

end CompressorRecords.ShrinkBundlePlan.Scheduled

end VPVNP
end Computability
end OAI
