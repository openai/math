import OAI.Computability.VPVNP.CompressorRecordsShrinkBuild
import OAI.Computability.VPVNP.CompressorShrinkLevelSpace
import OAI.Computability.VPVNP.CompressorScheduledSlotRates
import OAI.Computability.VPVNP.CompressorScheduledGreedyRates
import OAI.Computability.VPVNP.CompressorOrdinalProgress

/-!
# Uniform traffic of a complete admitted shrinking branch

The source trace includes the relocated greedy program, all dense rank and width
scans, the admitted motif calls, chosen scores, roles and preimages, and the
physical surviving-width and slot outputs. The coefficients precede the state
and its term choices.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ScheduledRates

open BurstRAM Compression Compression.PackingData Compression.ShrinkMotif
open PhaseCosts ShrinkBranch

open private packed_le motif_le selected_motifs positions_eq from
  OAI.Computability.VPVNP.CompressorShrinkLevelSpace

/-- The source-slot bound for the degree transition, evaluated on its fixed
role subdivisions and chosen output degree. -/
private noncomputable def transitionSlotRate (a b : ℕ) :=
  let d := 2 ^ a
  let c := Shrink.colors a
  let sub := subdivisions d c (2 ^ b)
  let u := 4*d*(2^c*d)*(∑ t, sub t)
  30+26*u+20*(2^b-survivingDegree d c sub)+44*2^b

/-- All shrinking reports up through the chosen role and preimage directories,
before the AB, surviving-width, and ordered-slot passes. -/
noncomputable def selectedRate {k : Type*} [_root_.Field k] {S : BlockSchedule k}
    (B : S.Templates) (a : ℕ) :=
  let d := 2 ^ a
  let Q := ShrinkRankSpace.cap a
  greedyRate d + 32 + (Q+53)*d + (50+TermRecordScan.probesPerRow B.shrink 2 8)*(d*Q)

/-- Complete source calls plus probes per incoming position. -/
noncomputable def completeRate {k : Type*} [_root_.Field k] {S : BlockSchedule k}
    (B : S.Templates) (a b : ℕ) :=
  let d := 2 ^ a
  let Q := ShrinkRankSpace.cap a
  let k₀ := TermRecordScan.probesPerRow B.shrink 2 8
  greedyRate d + 32 + (Q+53)*d + (50+k₀+18*ShrinkLevelSpace.subdivisionSum a b)*(d*Q)
    + transitionSlotRate a b

/-- Fixed deterministic clocks and the supplied admission clock. -/
def completeCap (a termCap : ℕ) :=
  max (max (max 66 (20+9*ShrinkRankSpace.cap a)) (CatalogRates.greedyShrinkCap (2 ^ a)))
    (max (ShrinkSliceSweep.SurvivingNative.ops.length+1) termCap)

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {a b g w : ℕ} {δ : ℝ} (X : State a (packingLaneBits a g))
variable (ready : Ready (2 ^ a) (Shrink.colors a) (2 ^ b) δ)
variable (T : IncidenceDirectory w) (start : ℕ) (stride selectors : Word w) (cap : ℕ)

private theorem scoreAxesCap (L : TermScores.Tables w) (n : ℕ) (as : List (TermScores.Axis w))
    (m : Memory w) (rs : List (Report w)) (h : TermScores.runAxes L n as m = some rs) :
    ∀ r ∈ rs, r.events.length+1 ≤ 27 := by
  induction as generalizing m rs with
  | nil =>
    have e : [] = rs := Option.some.inj h
    simp [← e]
  | cons a as ih =>
    simp only [TermScores.runAxes,Bind.bind] at h
    cases h₁ : runSegment (TermScores.workerMachine L a).program 27 (some 0) m
      (List.replicate n []) with
    | none => simp [h₁] at h
    | some first =>
      cases h₂ : TermScores.runAxes L n as (after m (eventLog first)) with
      | none => simp [h₁,h₂] at h
      | some last =>
        have e : first++last = rs := by simpa [h₁,h₂] using h
        subst rs
        intro r hr
        exact (List.mem_append.mp hr).elim (run_cap h₁ r) (ih _ _ h₂ r)

private theorem scoreCap (L : TermScores.Tables w) (n : ℕ) (as : List (TermScores.Axis w))
    (m : Memory w) (rs : List (Report w)) (h : TermScores.run L n as m = some rs) :
    ∀ r ∈ rs, r.events.length+1 ≤ 27 := by
  simp only [TermScores.run,TermScores.execute_clear,Bind.bind,Option.bind_some] at h
  let m₁ := after m (TermScores.clearReport L).events
  cases hs : TermScores.runAxes L n as m₁ with
  | none => rw [hs] at h; contradiction
  | some rows =>
    let m₂ := after m₁ (eventLog rows)
    rw [hs] at h
    simp only [Option.bind_some,TermScores.execute_compare, pure, Option.some.injEq] at h
    subst rs
    intro rep hr
    simp only [List.mem_cons,List.mem_append,List.mem_nil_iff,or_false] at hr
    rcases hr with rfl|hh|rfl
    · exact (by decide : 6+1 ≤ 27)
    · exact scoreAxesCap L n as m₁ rows hs rep hh
    · rw [(TermScores.compare_report_cost L m₂).1]; decide

private theorem inputClock {m : Memory w} (p : ShrinkInput.Run X T start m) (cap : ℕ) :
    ∀ r ∈ p.reports, r.events.length+1 ≤ completeCap a cap := by
  classical
  have fixed : 66 ≤ completeCap a cap :=
    ((le_max_left ..).trans (le_max_left ..)).trans (le_max_left ..)
  have rank : 20+9*ShrinkRankSpace.cap a ≤ completeCap a cap :=
    ((le_max_right ..).trans (le_max_left ..)).trans (le_max_left ..)
  have greedy : max 14 (CatalogRates.greedyShrinkCap (2^a)) ≤ completeCap a cap :=
    max_le ((by decide : 14 ≤ 66).trans fixed) ((le_max_right ..).trans (le_max_left ..))
  intro r hr
  simp only [ShrinkInput.Run.reports,List.mem_append] at hr
  rcases hr with (((((((((g|p₀)|cl)|cf)|ap)|ga)|rk)|sc)|th)|cd)|ab
  · exact ((greedyProgram X T start m p.greedy).2.2 r g).trans greedy
  · exact (run_cap p.positions r p₀).trans ((by decide : 65 ≤ 66).trans fixed)
  · exact (run_cap p.ranking.clear r cl).trans ((by decide : 8 ≤ 66).trans fixed)
  · exact (run_cap p.ranking.ranked.classify r cf).trans ((by decide : 66 ≤ 66).trans fixed)
  · exact (run_cap p.ranking.ranked.append r ap).trans ((by decide : 23 ≤ 66).trans fixed)
  · exact (run_cap p.ranking.ranked.gather r ga).trans ((by decide : 29 ≤ 66).trans fixed)
  · rw [(p.ranking.ranked.rank.calls r rk).2,PortRankRAM.visit_length]
    exact (by omega : 19+9*ShrinkRankSpace.cap a+1 ≤ 20+9*ShrinkRankSpace.cap a).trans rank
  · exact (run_cap p.widths.scatter r sc).trans ((by decide : 19 ≤ 66).trans fixed)
  · exact (run_cap p.widths.prefixes.thick.executed r th).trans ((by decide : 25 ≤ 66).trans fixed)
  · exact (run_cap p.widths.prefixes.motif.executed r cd).trans ((by decide : 25 ≤ 66).trans fixed)
  · exact (run_cap p.widths.ab r ab).trans ((by decide : 30 ≤ 66).trans fixed)

local notation "term" => ShrinkInput.termHead (w := w) X start
local notation "role" => SelectedArena.roleBase X term stride
local notation "retained" => SelectedFinish.stop X term stride
local notation "sh" => ShrinkSlots.levelShape (b := b) X
local notation "M" => ShrinkOutput.motifCount X

/-- Charge and instruction clock of the real pre-slice execution. The
coefficient depends on the transition degree and the finite term block. -/
theorem selectedReports {m : Memory w} {p : Prefix X T start cap m} {s : SelectedScore.Selection B X}
    (selected : Selected B X T start stride selectors cap m p s) :
    RAMBuckets.cost Report.probes (p.reports++selected.reports) ≤ X.positions*selectedRate B a ∧
      ∀ rep ∈ p.reports++selected.reports, rep.events.length+1 ≤ completeCap a cap := by
  classical
  let d := 2^a
  let Q := ShrinkRankSpace.cap a
  let N := Fintype.card X.Base
  let V := X.positions
  let P := ShrinkPreimages.newCount X
  let D := P*d
  let A := V*d
  let Tm := TermRecordScan.probesPerRow B.shrink 2 8
  let t := Greedy.WalkLayout.tagCount d
  let G := 16+7*d+8*d^2+5*t+8*t^2
  have hN : N ≤ V := by
    change Fintype.card X.Base ≤ X.positions
    rw [← positions_eq X]; exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have hP : P ≤ V := packed_le X
  have hD : D ≤ V*d := Nat.mul_le_mul_right _ hP
  have hM : ShrinkOutput.motifCount X ≤ V*(d*Q) := motif_le X
  have pre := p.input.reports_cost
  change RAMBuckets.cost Report.probes p.input.reports =
    2+N*G+9*ShrinkPreimages.oldCount X+4*D+(Q+33)*(ShrinkPreimages.oldCount X*d)+4*(ShrinkOutput.motifCount X) at pre
  rw [show ShrinkPreimages.oldCount X = V from positions_eq X] at pre
  have abs : RAMBuckets.cost Report.probes p.absolute = 5*A := by
    rw [p.absoluteRun.charge]; change 5*(ShrinkPreimages.oldCount X*d) = 5*A
    rw [show ShrinkPreimages.oldCount X = V from positions_eq X]
  have gather : RAMBuckets.cost Report.probes p.gather = 5*(ShrinkOutput.motifCount X) := by
    rw [SourceOnline.packet_cost,p.gatherRun.count,p.gatherRun.probes]; change (ShrinkOutput.motifCount X)+4*(ShrinkOutput.motifCount X) = 5*(ShrinkOutput.motifCount X); ring
  have terms : RAMBuckets.cost Report.probes selected.terms ≤ (ShrinkOutput.motifCount X)*(1+Tm) := by
    have n : ShrinkTermInputs.motifCount X = ShrinkOutput.motifCount X := selected_motifs X
    have small := selected.termRun.probes
    rw [n] at small
    rw [SourceOnline.packet_cost,selected.termRun.count,n,Nat.mul_add,Nat.mul_one]
    exact Nat.add_le_add_left small _
  have geometry := ChosenGeometry.Run.charge B X term stride selectors _ T s _ _
    selected.geometry selected.postTerm
  change RAMBuckets.cost Report.probes selected.geometry.reports =
    (40*SelectedArena.motifs X+7)+9*SelectedArena.positions X+11*DemandRAM.oldCount X+
      (2*P+5*ShrinkPreimages.oldCount X) at geometry
  rw [selected_motifs X,show SelectedArena.positions X = V from positions_eq X,
    show DemandRAM.oldCount X = A from congrArg (·*d) (positions_eq X),
    show ShrinkPreimages.oldCount X = V from positions_eq X] at geometry
  have eqRate : selectedRate B a = G+2+32+(Q+53)*d+(50+Tm)*(d*Q) := by
    dsimp only [selectedRate,greedyRate,G,d,Q,Tm,t]; ring
  constructor
  · simp only [Prefix.reports,Selected.reports,RAMBuckets.cost_append]
    rw [pre,abs,gather,geometry,eqRate]
    change _ ≤ V*_
    dsimp only [A] at *
    linarith only [terms,hD,hP,Nat.mul_le_mul_right G hN,X.positions_pos,
      Nat.mul_le_mul_right (50+Tm) hM]
  · have fixed : 66 ≤ completeCap a cap :=
      ((le_max_left ..).trans (le_max_left ..)).trans (le_max_left ..)
    have cap' : cap ≤ completeCap a cap := (le_max_right ..).trans (le_max_right ..)
    intro rep hr
    simp only [Prefix.reports,Selected.reports,
      ChosenGeometry.Construction.reports,SelectedStage.Passes.all,List.mem_append] at hr
    rcases hr with ((ip|ia)|ig)|(it|((hs|hp)|hd)|hc|hf)
    · exact inputClock X T start p.input cap rep ip
    · exact (run_cap p.absoluteRun.native rep ia).trans ((by decide : 25 ≤ 66).trans fixed)
    · exact (run_cap p.gatherRun.run rep ig).trans cap'
    · exact (run_cap selected.termRun.run rep it).trans cap'
    · exact (scoreCap _ _ _ _ _ selected.postTerm.placed.scores rep hs).trans
        ((by decide : 27 ≤ 66).trans fixed)
    · exact (run_cap selected.postTerm.placed.positions rep hp).trans
        ((by decide : 65 ≤ 66).trans fixed)
    · exact (run_cap selected.postTerm.placed.roles rep hd).trans
        ((by decide : 65 ≤ 66).trans fixed)
    · exact (run_cap selected.postTerm.geometry.raw.clear rep hc).trans
        ((by decide : 8 ≤ 66).trans fixed)
    · exact (run_cap selected.postTerm.geometry.raw.collect rep hf).trans
        ((by decide : 23 ≤ 66).trans fixed)

/-- A bound on the exact complete run built by `ShrinkBranch.build_complete`.
The returned coefficient and per-call clock are uniform over admitted branches. -/
theorem completeReports {m : Memory w} {p : Prefix X T start cap m}
    {s : SelectedScore.Selection B X} (r : Complete B X ready T start stride selectors cap m p s) :
    RAMBuckets.cost Report.probes r.reports ≤ X.positions*completeRate B a b ∧
      ∀ rep ∈ r.reports, rep.events.length+1 ≤ completeCap a cap := by
  classical
  let d := 2^a
  let Q := ShrinkRankSpace.cap a
  let V := X.positions
  let U := ShrinkLevelSpace.subdivisionSum a b
  have hM : M ≤ V*(d*Q) := motif_le X
  have selected := selectedReports B X T start stride selectors cap r.selected
  let bank := ShrinkOutput.splitBank (b := b) X B.shrink s term stride.val role retained
  let heads := ShrinkOutput.slotHeads (b := b) X (term).val stride.val role retained
  have slot := selectedSlotProgram X B.shrink ready s heads bank.widthBase T r.output.postWidths
    r.output.slots r.outputRun.construction.slots
  have slotWork : RAMBuckets.cost Report.probes r.output.slots.all ≤ V*transitionSlotRate a b := by
    have more := slot.2.1
    rw [RAMBuckets.cost_append] at more
    exact (Nat.le_add_right ..).trans more
  have out := r.outputRun.probes
  change RAMBuckets.cost Report.probes r.output.reports = 18*(M*U)+ShrinkOutput.slotProbes sh at out
  rw [← r.outputRun.construction.probes] at out
  have eqRate : completeRate B a b = selectedRate B a + 18*U*(d*Q) + transitionSlotRate a b := by
    dsimp only [completeRate,selectedRate,d,Q,U]; ring
  constructor
  · change RAMBuckets.cost Report.probes ((p.reports++r.selected.reports)++r.output.reports) ≤ _
    rw [RAMBuckets.cost_append,out,eqRate]
    linarith only [selected.1,slotWork,Nat.mul_le_mul_right (18*U) hM]
  · intro rep hr
    change rep ∈ (p.reports++r.selected.reports)++r.output.reports at hr
    rcases List.mem_append.mp hr with hi|ho
    · exact selected.2 rep hi
    have fixed : 66 ≤ completeCap a cap :=
      ((le_max_left ..).trans (le_max_left ..)).trans (le_max_left ..)
    rcases List.mem_append.mp ho with os|ot
    · obtain ⟨_,_,site⟩ := r.outputRun.sweep.sites os
      rw [site.length]; exact (le_max_left ..).trans (le_max_right ..)
    · exact (slot.2.2 rep (List.mem_append_left _ ot)).trans ((by decide : 49 ≤ 66).trans fixed)

end CompressorRecords.ScheduledRates

end VPVNP
end Computability
end OAI
