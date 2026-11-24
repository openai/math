import OAI.Computability.VPVNP.CompressorCompleteShrinkRates
import OAI.Computability.VPVNP.CompressorShrinkGeometryCharge
import OAI.Computability.VPVNP.CompressorShrinkScheduledPrefix

/-! # Traffic of the first thirty-six scheduled shrinking rows

The three header reports have a fixed charge. The greedy, placement,
bundle, term, and chosen-geometry workers use a bounded number of calls
and probes per old position. For the installed geometry group the two
score cursor conventions give the same events and number of calls.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkScheduledPrefix

open BurstRAM DescriptorSpace BlockPlanner PhaseRecipe Schedule SourceOnline Compression
open BlockHeaderRun ShrinkBlockInputs ScheduledRates ScheduledTrace
open scoped Fin.CommRing
open private publisherCounts from OAI.Computability.VPVNP.CompressorScheduledGreedyRates

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
variable (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps) {g w : ℕ}
variable (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X) (tape : List Bool)
variable (base : Word w) (positions blocks : ℕ) (old new : ℕ) (raw : Memory w)
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "v" => PairSimulation.TraversalRows.shrinkLevel B f hf i X sel tape
local notation "initialReports" => BlockHeaderRun.reports v L old new raw
local notation "pub₀" => BlockHeaderRun.scalarPorts (header w L old)
local notation "pub₁" => BlockHeaderRun.scalarPorts (header w L new)
local notation "pub₂" => BlockHeaderRun.headPorts (header w L new) (header w L 0)
local notation "inMem" => BlockHeaderRun.inputMemory v L old raw
local notation "outMem" => BlockHeaderRun.outputMemory v L old new raw

/-- Total calls and probes for the three header publications of this shrinking substep. -/
def fixedHeaderRate := headerRate (BlockProgram.geometry B) (.shrink (a i) (b i))
/-- Bound on one header report's event count plus the final instruction, used for private fuel. -/
def fixedHeaderCap := headerCap (BlockProgram.geometry B) (.shrink (a i) (b i))
/-- Per-old-position traffic coefficient for the first 36 shrinking visits, combining header
publication with the selected graph, term and geometry scans. -/
def prefixRate := fixedHeaderRate B i + selectedRate B (a i)

set_option maxHeartbeats 1100000 in
private theorem headerCharge :
    RAMBuckets.cost Report.probes initialReports = fixedHeaderRate B i ∧
      ∀ r ∈ initialReports, r.events.length+1 ≤ fixedHeaderCap B i := by
  let r₀ := scalarReport (inputRow v) (header w L old) (header w L old) raw
  let r₁ := scalarReport (outputRow v) (header w L old) (header w L new) inMem
  let r₂ := headReport L new outMem
  have h₀ := (publisherCounts (inputRow v) pub₀ (header w L old) raw).2
  have h₁ := (publisherCounts (outputRow v) pub₁ (header w L old) inMem).2
  have h₂ := (publisherCounts (DescriptorHeads.publisher (L).shape) pub₂ (0 : Word w) outMem).2
  change 1+r₀.probes = _ ∧ r₀.events.length+1 = _ at h₀
  change 1+r₁.probes = _ ∧ r₁.events.length+1 = _ at h₁
  change 1+r₂.probes = _ ∧ r₂.events.length+1 = _ at h₂
  constructor
  · change (1+r₀.probes)+(1+r₁.probes+(1+r₂.probes+0)) = _
    rw [h₀.1,h₁.1,h₂.1,Nat.add_zero,← Nat.add_assoc]
    rfl
  · intro r hr
    change r ∈ [r₀,r₁,r₂] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact h₀.2.le.trans (le_max_left ..)
    · exact h₁.2.le.trans ((le_max_left ..).trans (le_max_right ..))
    · exact h₂.2.le.trans ((le_max_right ..).trans (le_max_right ..))

variable (T : IncidenceDirectory w) (start : ℕ) (stride selectors : Word w) {fuel : ℕ} {m : Memory w}
variable {p : ShrinkBranch.Prefix X T start fuel m}
    (chosen : ShrinkBranch.Selected B X T start stride selectors fuel m p sel)

/-- Charge and clock of each actual source call, including all three
fixed header rows on the live input memories. -/
theorem raw_charge :
    RAMBuckets.cost Report.probes (initialReports++(p.reports++chosen.reports)) ≤
      fixedHeaderRate B i+X.positions*selectedRate B (a i) ∧
    ∀ r ∈ initialReports++(p.reports++chosen.reports),
      r.events.length+1 ≤ max (fixedHeaderCap B i) (completeCap (a i) fuel) := by
  obtain ⟨hc,ht⟩ := headerCharge B f hf i X sel tape base positions blocks old new raw
  obtain ⟨sc,st⟩ := selectedReports B X T start stride selectors fuel chosen
  refine ⟨?_,?_⟩
  · rw [RAMBuckets.cost_append,hc]
    exact Nat.add_le_add_left sc _
  · intro r hr
    exact (List.mem_append.mp hr).elim (fun hh ↦ (ht r hh).trans (le_max_left ..)) (fun hs ↦ (st r hs).trans (le_max_right ..))

local notation "scr" => BlockProgram.script B
local notation "Pkt₀" => SourceOnline.Packet scr w

/-- Apply the exact report and tape identities returned by the twenty-two
preparation and selection rows and the fourteen chosen-geometry rows. -/
theorem group_charge {pre geo : List Pkt₀} {last : Pkt₀} {mem : Memory w}
    (before : pre.flatMap SourceWalk.Packet.reports = initialReports++p.reports)
    (select : last.reports = chosen.terms) (preLen : pre.length=21) (geoLen : geo.length=14)
    (geoRun : SourceWalk.Chronological Visit.Runs mem geo)
    (events : eventLog (geo.flatMap SourceWalk.Packet.reports) = eventLog chosen.geometry.reports)
    (tapes : geo.flatMap (fun q ↦ q.stage.choices) = List.replicate (SelectedTailPackets.selectedCalls X) []) :
    let all := pre++last::geo
    RAMBuckets.cost Report.probes (all.flatMap SourceWalk.Packet.reports) ≤ fixedHeaderRate B i+X.positions*selectedRate B (a i) ∧
      all.length=36 ∧ groupCost scr all ≤ X.positions*groupRate scr (prefixRate B i) 36 := by
  intro all
  have gCost := SelectedTailPackets.geometry_cost_eq B X T start stride selectors chosen geoRun events tapes
  have sum := (raw_charge B f hf i X sel tape base positions blocks old new raw T start stride selectors chosen).1
  have data : RAMBuckets.cost Report.probes (all.flatMap SourceWalk.Packet.reports) ≤ fixedHeaderRate B i+X.positions*selectedRate B (a i) := by
    simp only [all,List.flatMap_append,List.flatMap_cons,before,select,RAMBuckets.cost_append,gCost]
    simp only [ShrinkBranch.Selected.reports,RAMBuckets.cost_append] at sum
    omega
  have len : all.length=36 := by simp only [all,List.length_append,List.length_cons,preLen,geoLen]
  refine ⟨data,len,groupCost_le scr all _ _ _ ?_ ?_⟩
  · apply data.trans
    rw [prefixRate,Nat.mul_add]
    exact Nat.add_le_add_right (Nat.le_mul_of_pos_left _ X.positions_pos) _
  · rw [len]
    exact Nat.le_mul_of_pos_left _ X.positions_pos

/-- Each actual scheduled source report obeys the clock proved for its
catalog occurrence, including the redirected score reports. -/
theorem group_tick_bound {ps : List Pkt₀} {cap ordinal total : ℕ} {mem : Memory w}
    (group : Group scr L base cap ordinal total mem ps) (r : Report w) (hr : r ∈ ps.flatMap SourceWalk.Packet.reports) :
    r.events.length+1 ≤ cap := by
  obtain ⟨packet,hp,hreport⟩ := List.mem_flatMap.mp hr
  have runs {A : Script} {raw : Memory w} {qs : List (SourceOnline.Packet A w)} (chron : SourceWalk.Chronological Visit.Runs raw qs) :
      ∀ q ∈ qs, q.stage.Runs q.input q.reports := by
    induction qs generalizing raw with
    | nil => simp
    | cons q qs ih =>
      intro b hb
      exact (List.mem_cons.mp hb).elim (fun e ↦ e ▸ chron.2.1) (fun h ↦ ih chron.2.2 b h)
  have length := localSegment_event_bound ((runSegment_iff ..).mp (runs group.chronological packet hp)).1 r hreport
  have bound := (group.checked packet hp).dataClock
  omega

end CompressorRecords.ShrinkScheduledPrefix

end

end VPVNP
end Computability
end OAI
