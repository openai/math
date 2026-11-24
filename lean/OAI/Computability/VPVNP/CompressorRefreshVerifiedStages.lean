import OAI.Computability.VPVNP.CompressorRefreshMiddleRecords
import OAI.Computability.VPVNP.CompressorRefreshExternalReplay
import OAI.Computability.VPVNP.CompressorRefreshTermDataFrame
import OAI.Computability.VPVNP.CompressorRefreshIncidenceWorkerSafety
import OAI.Computability.VPVNP.CompressorRefreshStageVisits
import OAI.Computability.VPVNP.CompressorTermWorkerFootprint
import OAI.Computability.VPVNP.CompressorSourceZip

/-!
# Cursor and address checks for the complete native refresh schedule

The certified walk follows the actual selected term tape through the external
scans, demands, term row, supplies, fixed expander, slot scans and final base rows.
Old columns supply the first two scans. Every remaining access stays inside the
packed level. The resulting checks can be attached to the global online calendar.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace CompressorRecords.PortRefresh.Scheduled

open BurstRAM PrimedStackRAM Compression Compression.Refresh Compression.DegreeRefresh SpectralGeometry
open LevelRecipe NewSlots Allocation StageFrame SourceTransport
open scoped Fin.CommRing
open private bounds from OAI.Computability.VPVNP.CompressorRecordRefreshBuild

variable {w a a₀ g dH t : ℕ} {k : Type*} [_root_.Field k] {K K' : ℝ}
variable (X : State a (a+g)) (E : RegularArcGraph (Fin (2^a)) dH) (hdH : 0 < dH)
  (conn : (arcSupportGraph E.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply E hdH conn) (2^a₀) K K')
  (hD : 1 < 2^a) (hd : dH+1 ≤ 2^a₀) (c : DyadicRefreshChoice X E hdH conn F)
  (ties : Fin t ≃ Tie (2^a)) (old : IncidenceDirectory w) (start stride : ℕ)
local notation "P" => plan X a₀ dH t stride start
local notation "I" => Plan.inputs P w
local notation "T" => Plan.output P w
local notation "Q" => Plan.scratch P w
local notation "S₀" => shape (t := t) E hdH conn F stride
local notation "J" => Stage S₀
local notation "D" => word (bits := w) (Plan.demand P)
local notation "M" => word (bits := w) (Plan.term P)
local notation "Y" => dyadicRefreshNext X E hdH conn F hD hd c
local notation "src" => Source X E hdH conn F hd c ties old start stride
local notation "area" => TermDataFrame.InArena P

/-- The reports span the selected stage's cursor interval, read only at or above the lower
address bound and write only within the refresh allocation. -/
def StageBounds (low : ℕ) (j : J) (_ : Memory w) (rs : List (Report w)) : Prop :=
  Scanned j.first (j.limit X start) rs ∧ Reads (low ≤ ·) (eventLog rs) ∧ Writes area (eventLog rs)

local notation "checked" => StageBounds (t := t) X E hdH conn F start stride

private theorem lift_bounds {first N low : ℕ} {rs : List (Report w)} {r s write : ℕ → Prop}
    (x : Scanned first N rs ∧ Reads r (eventLog rs) ∧ Writes s (eventLog rs))
    (rd : ∀ a, r a → low ≤ a) (wr : ∀ a, s a → write a) :
    Scanned first N rs ∧ Reads (low ≤ ·) (eventLog rs) ∧ Writes write (eventLog rs) :=
  ⟨x.1,fun a v h ↦ rd _ (x.2.1 a v h),fun a v h ↦ wr _ (x.2.2 a v h)⟩

private theorem term_bounds (L : PrepareLayout X old a₀ dH t stride start) (low cap : ℕ)
    (low_le : low ≤ start) (wide : 2+2^a*dH ≤ stride) (room : (P).stop < 2^w)
    (m : Memory w) (rs : List (Report w))
    (run : termRun E hdH conn F ties X D M stride cap (blockTapes E hdH conn F X c w) m = some rs) :
    checked low .term m rs := by
  let B := (P).blocks
  let n := 2^a*dH
  let b := termAddresses D M stride t
  let ord := (finProdFinEquiv (m := 2^a) (n := dH)).symm
  let L₀ := termRows X D M stride wide L.demandTerm L.termRoom
  let prog := TermWorker.program F ties ord b
  let tape := List.ofFn (blockTapes E hdH conn F X c w)
  have rt : runSegment prog cap (some (0 : W w)) m tape = some rs := run
  have has := TermWorker.addresses_strided (m := B) (d := t) (n := n) (D).val (M).val t stride le_rfl wide L.demandTerm L.termRoom
  have len : 0+tape.length=B := by simp [tape,B,plan]
  have shape := scanned_tapes prog cap B (fun j hj mem bs rep hr ↦ by
    let i : Fin B := ⟨j,hj⟩
    obtain ⟨s,u⟩ := has i
    have sourceFits : (TermWorker.source b (word j)).val+t ≤ 2^w := s.symm ▸ L₀.sourceFits i
    have destFits : (TermWorker.base b (word j)).val+2+n < 2^w := u.symm ▸ L₀.termFits i
    simpa only [Nat.cast_add_one,word,Fin.ofNat_eq_cast] using (TermWorker.Footprint.call F ties ord b (word j) mem cap bs rep sourceFits destFits hr).1)
      0 m tape rs len rt
  have fp := TermWorker.Footprint.strided_segment F ties ord (D).val (M).val t stride le_rfl wide
    L.demandTerm L.termRoom 0 cap m tape rs len.le rt
  have ht : (P).term ≤ (P).stop := by dsimp only [Plan.stop,Plan.next,Plan.reverseSlot,Plan.targetPort,Plan.supply]; omega
  have hd : (P).demand ≤ (P).term := Nat.le_add_right ..
  have ds : (D).val = (P).demand := Nat.mod_eq_of_lt (hd.trans_lt (ht.trans_lt room))
  have ms : (M).val = (P).term := Nat.mod_eq_of_lt (ht.trans_lt room)
  have lower : start ≤ (P).demand := Nat.le_add_right ..
  have top : (M).val+B*stride ≤ (P).stop := by
    rw [ms]
    change (P).supply ≤ (P).stop
    dsimp only [Plan.stop,Plan.next,Plan.reverseSlot,Plan.targetPort]; omega
  exact lift_bounds ⟨shape,fp⟩ (fun x hx ↦ low_le.trans (lower.trans (ds ▸ hx.1)))
    (fun x hx ↦ ⟨lower.trans (hd.trans (ms ▸ hx.1)),hx.2.trans_le top⟩)

private theorem demand_bounds (low : ℕ) (low_le : low ≤ start) (room : (P).stop < 2^w)
    {ks : List (Fin t)} {m : Memory w} {rs : List (Report w)}
    (run : DemandScan.Runs (DemandScan.words (r := 2^g) ties Q D) (P).blocks ks m rs) :
    SourceWalk (checked low) (ks.map Stage.demand) m rs := by
  induction run with
  | nil => exact .done _
  | cons j h _ ih =>
    have scan := TermDataFrame.demand_trace X a₀ dH stride start ties room j _ _ h
    exact .next (lift_bounds scan (fun _ h ↦ low_le.trans h.1) (fun _ h ↦ h)) ih

private theorem rom_bounds (low : ℕ) (low_le : low ≤ start) (room : (P).stop < 2^w)
    (js : List (Fin (2^a*dH))) (m : Memory w) :
    SourceWalk (checked low) (js.map Stage.rom) m (js.map (ExpanderROM.report E I)) := by
  induction js generalizing m with
  | nil => exact .done _
  | cons j js ih =>
    have scan := TermDataFrame.rom_trace (t := t) X a₀ dH stride start E room j m
    change SourceWalk _ _ _ ([ExpanderROM.report E I j] ++ _)
    exact .next (lift_bounds scan (fun _ h ↦ low_le.trans h.1) (fun _ h ↦ h)) (ih _)

private theorem slot_bounds (low : ℕ) (low_le : low ≤ start) (room : (P).stop < 2^w)
    (fit : AllSlots.Fits (a₀ := a₀) X w) (ref : Memory w) (sourceTables : AllSlots.SourceTables X E hdH conn F c I ref)
    {ks : List (Fin (2^a₀))} {m : Memory w} {rs : List (Report w)}
    (agree : IncidenceWorkerSafety.SlotInvariant P ref m)
    (run : AllSlots.Runs (fun j ↦ kindOf ((refreshSlots hd).symm j))
      (fun j ↦ AllSlots.words (2^a) (2^g) I T ((refreshSlots hd).symm j)) (P).sites ks m rs) :
    SourceWalk (checked low) (ks.map Stage.slot) m rs := by
  induction run with
  | nil => exact .done _
  | cons j h _ ih =>
    obtain ⟨shape,ag,fp⟩ := IncidenceWorkerSafety.slot_scan (t := t) (stride := stride) (start := start)
      X E hdH conn F hd c ((refreshSlots hd).symm j) fit room.le ref _ sourceTables agree _ h
    exact .next (lift_bounds ⟨shape,fp⟩ (fun _ h ↦ low_le.trans h.1) (fun _ h ↦ h)) (ih ag)

/-- All raw stages of the selected physical execution, together with their
scheduler guards and concrete data read/write bounds. -/
theorem verified_sources (low cap : ℕ) (L : PrepareLayout X old a₀ dH t stride start)
    (m : Memory w) (rs : List (Report w)) (rep : old.Represents X m)
    (oldAbove : ∀ j, low ≤ (old.column j).val)
    (before : ∀ j, (old.column j).val+(P).segments ≤ start)
    (wide : 2+2^a*dH ≤ stride) (room : (P).stop < 2^w)
    (termBits : termConstant E hdH conn F ties + 4*Nat.clog 2 (X.maxWireWidth+1) ≤ w)
    (nextWidth : (Y).maxWireWidth < 2^w) (capFit : TermWorker.budget F t (2^a*dH) w X.maxWireWidth ≤ cap)
    (run : Build.Run X E hdH conn F hD hd c ties old start stride cap L m rs) :
    SourceWalk (fun j mem logs ↦ src cap j mem logs ∧ checked low j mem logs) (order S₀) m rs := by
  have raw := sources X E hdH conn F hD hd c ties old start stride cap L m rs run
  apply raw.zip _ rfl (fun j mem xs ys h₁ h₂ ↦ (source_calls X E hdH conn F hd c ties old start stride h₁).trans
    (StageFrame.Scanned.length h₂.1).symm)
  obtain ⟨pre,terms,post,rfl,hpre,hterm,hpost⟩ := run
  let m₁ := after m (eventLog pre)
  let m₂ := after m₁ (eventLog terms)
  have mid := Build.middle_records X E hdH conn F hD hd c ties old start stride L m m₁ rep pre terms hpre wide room
    termBits nextWidth cap capFit hterm
  obtain ⟨su,roms,os,bs,rfl,hs,hr,ho,hb⟩ := hpost
  have afterTerm := Build.output_records (t := t) X E hdH conn F hD hd c start stride m₂ su roms os wide room nextWidth
    L.regions.fits mid.2.1 mid.2.2 hs hr ho
  have low_le : low ≤ start := (oldAbove 0).trans ((Nat.le_add_right ..).trans (before 0))
  have lowOld (x) (hx : FrontFrame.OldCell old (P).segments x) : low ≤ x := by
    obtain ⟨j,hj,_⟩ := hx
    exact (oldAbove j).trans hj
  have lowArena (x) (hx : area x) : low ≤ x := low_le.trans hx.1
  have next := finish_layout X E hdH conn F hD hd c t stride start wide room.le
  have hterm' := term_bounds X E hdH conn F c ties old start stride L low cap low_le wide room m₁ terms hterm
  have hsup := TermDataFrame.supply_trace (t := t) X a₀ dH stride start E hdH conn F room wide m₂ su hs
  have htermSu : SourceWalk (checked low) [.term,.supply] m₁ (terms++su) :=
    .next hterm' (.singleton (lift_bounds hsup lowArena (fun _ h ↦ h)))
  let m₃ := after m₂ (eventLog su)
  have he' := ExpanderROM.schedule_run E I 0 m₃ (List.finRange (2^a*dH))
  have same := Option.some.inj (hr.symm.trans he')
  have hw₃ := rom_bounds (t := t) X E hdH conn F start stride low low_le room (List.finRange _) m₃
  rw [← same] at hw₃
  let m₄ := after m₃ (eventLog roms)
  have hw₄ := slot_bounds X E hdH conn F hd c start stride low low_le room next.dims m₄ afterTerm.1 (fun _ _ ↦ rfl) ho
  have cap_eq : BaseOutput.actualCount (Y) = (P).capacity := by
    change Fintype.card (X.Base × Fin (2^a)) * 2^g * 2^a₀ = _
    simp only [Fintype.card_prod,Fintype.card_fin]; rfl
  obtain ⟨baseShape,_,baseFp⟩ := IncidenceWorkerSafety.base_scan (P) (Y) cap_eq room.le next.incidence
    (after m₄ (eventLog os)) afterTerm.2 bs hb
  have hsize : BaseOutput.baseCount (Y) = Fintype.card X.Base*2^a*2^a₀ := by
    change Fintype.card (X.Base × Fin (2^a))*2^a₀ = _
    simp only [Fintype.card_prod,Fintype.card_fin]
  rw [hsize] at baseShape
  have hw₅ : SourceWalk (checked low) [.base] (after m₄ (eventLog os)) bs :=
    .singleton (lift_bounds ⟨baseShape,baseFp⟩ lowArena (fun _ h ↦ h))
  have tail := hw₃.append (hw₄.append hw₅)
  have rest := htermSu.append (by simpa only [SourceWalk.after_append] using tail)
  obtain ⟨rg,rd,re,ds,ext,dem,_,rfl⟩ := hpre
  have extFit := FrontFrame.external_scans X old a₀ dH t stride start before room
    (bounds X E hdH conn F hD hd c nextWidth).1 m rep rg rd re L.regions.fits ext
  let m₀ := after (after (after m (eventLog rg)) (eventLog rd)) (eventLog re)
  have hfirst : SourceWalk (checked low) [.gather,.bundles,.offsets] m (rg++rd++re) := by
    rw [List.append_assoc]
    exact .next (lift_bounds extFit.1 lowOld (fun _ h ↦ h)) (.next (lift_bounds extFit.2.1 lowOld (fun _ h ↦ h))
      (.singleton (lift_bounds extFit.2.2 lowArena (fun _ h ↦ h))))
  have hdem := demand_bounds X E hdH conn F ties start stride low low_le room dem
  have hdemRest := hdem.append (by simpa only [m₁,SourceWalk.after_append] using rest)
  have full := hfirst.append (by simpa only [SourceWalk.after_append] using hdemRest)
  simpa only [order,List.append_assoc] using full

end CompressorRecords.PortRefresh.Scheduled

end

end VPVNP
end Computability
end OAI
