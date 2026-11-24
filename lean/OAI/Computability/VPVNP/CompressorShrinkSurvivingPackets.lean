import OAI.Computability.VPVNP.CompressorShrinkAllocatedTables
import OAI.Computability.VPVNP.CompressorShrinkSlotPacketSpace
import OAI.Computability.VPVNP.CompressorShrinkABSliceWindow
import OAI.Computability.VPVNP.CompressorShrinkPreparationAccess
import OAI.Computability.VPVNP.CompressorSourceScanned
import OAI.Computability.VPVNP.CompressorShrinkSurvivingOperands

/-!
# The four surviving-width packets in a shrinking block

Each role's native worker reads the chosen bit at the common score address,
the absolute arc ID and the two term words. It writes the balanced subdivision
width and its interval references in table two. The four chronological packets
retain the original reports and start in the memory produced by the AB scans.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.SurvivingPackets

open BurstRAM Compression PhaseRecipe BlockPlanner DescriptorSpace Schedule SourceTransport
open ShrinkSliceSweep ShrinkBlockInputs SurvivingNative
open scoped Fin.CommRing
open private scanned from OAI.Computability.VPVNP.CompressorShrinkPreparationAccess
open private useFixedFuel from OAI.Computability.VPVNP.CompressorScheduledSliceRates
open private expr_agree from OAI.Computability.VPVNP.CompressorShrinkABSliceWindow

/-- One more than the length of the native surviving-width instruction list, allowing the final
return. -/
abbrev workerFuel := 1+SurvivingNative.ops.length

variable {w n A : ℕ} {L : Layout} {D : ℕ → Prop} {pub : Fin 5 → Word w} {st : Word w}

/-- The public recipe for each role has the same operands as the physical
allocation. All planner loads consult the reference header below table zero. -/
def Evaluated (heads : Heads) (T : Allocation w n A) (abs layout : Word w) (cut : ℕ) (ref : Memory w)
    (D : ℕ → Prop) (pub : Fin 5 → Word w) (st : Word w) : Prop :=
  ∀ t, let v := SurvivingNative.visits T.subdiv heads t
    (v.initial.eval pub st ref = 0 ∧ v.stop.eval pub st ref = ((n*T.subdiv t : ℕ) : Word w) ∧
      (fun i ↦ (v.params i).eval pub st ref) = params T t abs layout) ∧
      HeaderOperands.Supported (fun x ↦ D x ∧ x < cut) pub st ref v

/-- The finite native traces feed the actual header-driven visits. Shortening
the per-call clock to the worker's instruction count preserves every report. -/
theorem raw_walk (heads : Heads) (T : Allocation w n A) (abs layout : Word w) (cut : ℕ) (ref : Memory w)
    (fit : T.Fits) (low : levelStart L 0 ≤ cut) (writesAbove : cut ≤ T.widthBase)
    (readsAbove : ∀ x, readRegion T abs layout x → levelStart L 0 ≤ x)
    (values : Evaluated heads T abs layout cut ref D pub st)
    {f : ℕ} {width : Allocation.Id n → ℕ} {js : List (Fin 4)} {mem out : Memory w} {batches : List (List (Report w))}
    (raw : SurvivingPass.Roles T width (fun t ↦ program T t abs layout) (fun _ ↦ f)
      (fun t ↦ Site T t abs layout) js mem out batches) (same : Agree (· < cut) ref mem) :
    SourceWalk (fun v cur rs ↦ ∃ bits,
      HeaderPacket.Run L pub st v cur rs workerFuel bits ∧ HeaderOperands.Supported D pub st cur v)
      (js.map (SurvivingNative.visits T.subdiv heads)) mem batches.flatten := by
  induction raw with
  | nil => exact .done _
  | @cons t ts mem out rs batches run _ ih =>
    let v := SurvivingNative.visits T.subdiv heads t
    let data := params T t abs layout
    let M := program T t abs layout
    let N := n*T.subdiv t
    have actual : runSegment M workerFuel (some 0) mem (List.replicate N []) = some rs :=
      useFixedFuel M (fun m i ↦ ⟨_,(SurvivingNative.native data i m).1⟩) run.executed
    have inc (m : Memory w) (i : Word w) (r : Report w)
        (he : execute M workerFuel (M.start i) m [] = some r) : r.result = some (i+1) :=
      (congrArg Report.result (Option.some.inj (he.symm.trans (SurvivingNative.native data i m).1))).trans
        (SurvivingNative.native data i m).2.1
    have scan : StageFrame.Scanned 0 N rs := by simpa only [Nat.zero_add] using scanned inc mem 0 N rs actual
    obtain ⟨eval,supported⟩ := values t
    have start := expr_agree v.initial D cut mem supported.initial same
    have stop := expr_agree v.stop D cut mem supported.stop same
    have args (j) := expr_agree (v.params j) D cut mem (supported.params j) same
    have eqStart := start.1.symm.trans eval.1
    have eqStop := stop.1.symm.trans eval.2.1
    have eqArgs : (fun j ↦ (v.params j).eval pub st mem) = data :=
      (funext fun j ↦ (args j).1.symm).trans eval.2.2
    obtain ⟨rd,wr⟩ := run.toSegment.footprint (fun r (h : Site T t abs layout r) ↦ ⟨h.reads,h.writes⟩)
    have later (x : ℕ) (hx : writeRegion T t x) : cut ≤ x := by
      obtain ⟨i,inside⟩ := hx
      exact le_of_not_gt (fun h ↦ inside (T.rowOutside fit (i,t) x (.inl (h.trans_le writesAbove))))
    have agree : Agree (· < cut) ref (after mem (eventLog rs)) := fun x hx ↦
      (same x hx).trans (after_outside mem wr (fun h ↦ (later x h).not_gt hx)).symm
    refine .next ⟨List.replicate N [],⟨Nat.zero_lt_succ _,?_,?_,fun a b ha ↦ readsAbove _ (rd a b ha),
      fun a b ha ↦ low.trans (later _ (wr a b ha))⟩,⟨start.2,stop.2,fun j ↦ (args j).2⟩⟩ (ih agree)
    · change runSegment (v.worker.table.instantiate w (fun j ↦ (v.params j).eval pub st mem)).program
        workerFuel (some (v.initial.eval pub st mem)) mem (List.replicate N []) = _
      rw [eqStart,eqArgs]
      exact actual
    · change SourceOnline.Progress (v.stop.eval pub st mem) (v.initial.eval pub st mem) rs
      rw [eqStop,eqStart]; exact scan.toProgress (count_fit T fit t)

section Physical

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (inc : IncidenceDirectory w)
variable (base : Word w) (positions blocks round : ℕ)

local notation "scr" => BlockProgram.script B
local notation "geom" => BlockProgram.geometry B
local notation "lay" => BlockProgram.layout B base.val positions blocks
local notation "ports" => Workspace.ports (Schedule.arity (Script.catalog (BlockProgram.script B))) base
local notation "public" => Schedule.Ports.data ports
local notation "blockStart" => (S.steps+1)*round
local notation "cur" => blockStart+i.val
local notation "state" => (levelStart lay blockStart : Word w)
local notation "cut" => tableBase lay cur (0 : Fin 6)
local notation "ab" => tableBase lay cur (1 : Fin 6)
local notation "width" => tableBase lay cur (2 : Fin 6)
local notation "slots" => tableBase lay cur (3 : Fin 6)
local notation "term" => ShrinkInput.termHead (w := w) X cut
local notation "stride" => (10 : Word w)
local notation "oldRole" => SelectedArena.roleBase X term stride
local notation "layoutAddr" => ShrinkOutput.layoutWord X term stride
local notation "ids" => ShrinkBundlePlan.absoluteHead (ShrinkInput.plan X cut) w
local notation "heads" => BlockSlices.survivingHeads B geom i (BlockProgram.arena B i.val 0) (BlockProgram.arena B i.val 2)
local notation "high" => levelStart lay 0
local notation "data" => Window.operandRegion scr lay base
local notation "V" => BlockSlices.surviving B geom i (BlockProgram.arena B i.val 0) (BlockProgram.arena B i.val 2)

/-- The four surviving-width visits for the supply roles, placed in the script immediately
after the AB intersection scans. -/
abbrev window : Window scr V := BlockGroups.shrink B i 7

private theorem absolute_low (start : ℕ) (room : ShrinkInput.termEnd X start 10 < 2^w) :
    start ≤ (ShrinkBundlePlan.absoluteHead (ShrinkInput.plan X start) w).val := by
  let z := ShrinkInput.plan X start
  obtain ⟨hg,hp,_,hw⟩ := ShrinkInput.range_bounds X start
  have rect : z.rectangleSize = 2*(z.B*z.Q) := Nat.mul_assoc ..
  have startRank : start ≤ z.origin := hg.trans hp
  have lo : z.origin ≤ z.gathered := by unfold ShrinkRankSpace.Shape.gathered ShrinkRankSpace.Shape.ids ShrinkRankSpace.Shape.counts; omega
  have stop : z.stop ≤ ShrinkInput.stop X start := hw
  change z.gathered+z.rectangleSize+z.A ≤ _ at stop
  rw [rect] at stop
  unfold ShrinkInput.termEnd at room
  change start ≤ (z.gathered+z.B*z.Q)%(2^w)
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

variable (sel : SelectedScore.Selection B X) {δ : ℝ} (ready : ShrinkMotif.Ready (2^(a i)) (Shrink.colors (a i)) (2^(b i)) δ)

local notation "alloc" => ShrinkOutput.splitBank (b := b i) X B.shrink sel term (Fin.val stride) oldRole width
local notation "win" => window B i

set_option maxHeartbeats 1200000 in
/-- Package the four actual surviving segments of the chosen `withAB` run.
Their source memory starts after its AB reports and ends at the exact width
memory consumed by the following ordered-slot construction. -/
theorem group (ref mem : Memory w) (srcFuel onlineCap : ℕ) (r : ShrinkOutput.TablesRun w)
    (complete : ShrinkOutput.CompleteTables B i X ready sel term stride ids cut
      (BlockSlices.abInputs i (BlockProgram.arena B i.val 0) (BlockProgram.arena B i.val 1)) public state ref
      ab width slots srcFuel mem r)
    (live : round < blocks) (capacity : X.positions ≤ positions) (room : endAddress lay < 2^w)
    (header : ShrinkHeaderReads.Header i X inc cut lay blockStart mem)
    (widthHead : mem (levelStart lay cur+62) = (width : Word w))
    (total : mem (ports).rows.val = (directoryRows lay : Word w))
    (pitch : mem ((ports).directory-1).val = (levelWords lay : Word w))
    (clock : SourceOnline.scanCap scr workerFuel ≤ onlineCap) :
    ∃ ps : List (SourceOnline.Packet scr w), SourceOnline.Group scr lay base onlineCap
      ((scr).initial.length+round*(scr).block.length+(win).before.length) (directoryRows lay) (r.postAB mem) ps ∧
      ps.map (fun p ↦ p.stage.phase) = (win).indices ∧ ps.flatMap SourceWalk.Packet.reports = r.remainder.widthRows.flatten ∧
      SourceOnline.post (r.postAB mem) ps = r.remainder.postWidths := by
  have boundary := ShrinkSlotCalendar.physical_boundary B i X base positions blocks round live capacity room
  have size : X.positions*ShrinkLevelSpace.tableFactor S ≤ tableWords lay := by
    have degree : 2^(a i) ≤ slotDegree S :=
      (Finset.le_sup (f := fun j : Fin (S.steps+1) ↦ 2^S.degreeExponent j) (Finset.mem_univ i.castSucc)).trans
        (le_max_right ..)
    have hc : ShrinkLevelSpace.tableFactor S ≤ BlockProgram.fieldCount B :=
      (le_max_left ..).trans (Nat.le_add_right ..)
    change _ ≤ positions*slotDegree S*BlockProgram.fieldCount B
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul capacity (hc.trans (Nat.le_mul_of_pos_left _ ((Nat.two_pow_pos _).trans_le degree)))
  have ends := ShrinkLevelSpace.packed_ends S i X cut ab width slots w
  have cutToWidth := tableEnd_le_tableBase lay cur (show (0 : Fin 6) < 2 by decide)
  have widthToSlots := tableEnd_le_tableBase lay cur (show (2 : Fin 6) < 3 by decide)
  have startToAB := tableEnd_le_tableBase lay cur (show (0 : Fin 6) < 1 by decide)
  have headBefore : levelStart lay cur+62 < cut := by
    change _ < levelStart lay cur+66+6*slotCapacity lay+0*tableWords lay
    omega
  have hcut : high ≤ cut := (levelStart_mono lay (Nat.zero_le cur)).trans (by omega)
  have slotRoom : slots < 2^w := by
    have nxt : levelStart lay (cur+1)+66 ≤ 2^w := by
      rw [Nat.add_assoc]; exact boundary.nextFits
    have e := tableEnd_le_nextLevel lay cur (3 : Fin 6)
    omega
  have termFit : ShrinkInput.termEnd X cut 10 < 2^w := ends.2.1.trans_lt (by omega)
  have early : SelectedFinish.stop X term stride ≤ width := ends.2.2.1.trans
    ((Nat.add_le_add_left size cut).trans cutToWidth)
  have baseEq : (alloc).widthBase = width := ShrinkOutput.width_at_eq i X term stride width early
  have last : (alloc).last ≤ slots := by
    change ShrinkOutput.slotsBase X (alloc).widthBase (ShrinkSlots.levelShape (b := b i) X) ≤ _
    rw [baseEq]
    exact ends.2.2.2.2.2.1.trans ((Nat.add_le_add_left size width).trans widthToSlots)
  have ten : (10 : ℕ) < 2^w := by have hh := header.room; omega
  have allocationFits : (alloc).Fits := ⟨(Nat.mod_eq_of_lt ten).ge, le_max_left .., ready.count_pos,
    last.trans_lt slotRoom,by omega⟩
  have entry : LevelFields.Entry lay blockStart public state mem := ⟨rfl,pitch⟩
  have supported : Evaluated heads alloc ids layoutAddr cut mem data public state := fun t ↦
    ShrinkSurvivingOperands.fields B i X inc cut sel width public state mem header entry termFit early widthHead
      headBefore (boundary.pitchBefore.trans_le hcut) data (.inr (.inl rfl)) (fun _ h ↦ .inr (.inr h)) t
  have highRead (x : ℕ) (hx : readRegion alloc ids layoutAddr x) : high ≤ x := by
    rcases hx with rfl | ⟨lo,_⟩ | ⟨j,lo,_⟩
    · have hv := Nat.mod_eq_of_lt (boundary.scoreBefore.trans slotRoom)
      exact (show (layoutAddr).val = _ from hv) ▸ boundary.scoreHigh
    · exact hcut.trans ((absolute_low i X cut termFit).trans lo)
    · exact hcut.trans ((ScorePackets.start_le_term i X cut termFit).trans ((Nat.le_add_right ..).trans lo))
  have agree : Agree (· < cut) mem (r.postAB mem) := fun x hx ↦ (complete.abFrame x (.inl (by omega))).symm
  have ww := raw_walk heads alloc ids layoutAddr cut mem allocationFits hcut (by rw [baseEq]; omega)
    highRead supported complete.remainder.sweep agree
  have raw : SourceWalk (Window.Raw (A := scr) lay base round workerFuel) V (r.postAB mem) r.remainder.widthRows.flatten := by
    have lift {js : List BlockPlanner.Visit} {mm : Memory w} {xs : List (Report w)}
        (walk : SourceWalk (fun v m rs ↦ ∃ bits, HeaderPacket.Run lay public state v m rs workerFuel bits ∧
          HeaderOperands.Supported data public state m v) js mm xs) :
        SourceWalk (Window.Raw (A := scr) lay base round workerFuel) js mm xs := by
      induction walk with
      | done => exact .done _
      | next hd _ ih => obtain ⟨bs,rn,ok⟩ := hd; exact .next ⟨workerFuel,bs,le_rfl,rn,ok⟩ ih
    exact lift ww
  have rowEq := (agree _ (boundary.rowsBefore.trans_le hcut)).symm.trans total
  have pitchEq := (agree _ (boundary.pitchBefore.trans_le hcut)).symm.trans pitch
  have ord (j : Fin (V).length) : Window.ordinal (A := scr) round ((win).index j) < directoryRows lay := by
    rw [(win).ordinal_index]
    have hr := boundary.blockRoom
    rw [Nat.succ_mul] at hr
    have hi := ((win).position j).isLt
    omega
  have clocks (j : Fin (scr).size) :
      ((scr).plan.recipes j).2.code.length+1+2*Online.N (scr).size (scr).size+5 ≤ onlineCap ∧
      workerFuel+3+4*(((scr).catalog j).params+1)+2*Online.N (scr).size (scr).size+5 ≤ onlineCap := by
    have rc := Finset.le_sup (f := fun j : Fin (scr).size ↦ ((scr).plan.recipes j).2.code.length+1+
      2*Online.N (scr).size (scr).size+5) (Finset.mem_univ j)
    have ar := params_le_arity (scr).catalog j
    unfold SourceOnline.scanCap at clock
    exact ⟨rc.trans ((le_max_left ..).trans clock),by omega⟩
  obtain ⟨ps,hgroup,hids,hrs⟩ := (win).group lay base round rfl rfl boundary.fits onlineCap workerFuel
    (r.postAB mem) r.remainder.widthRows.flatten raw rowEq pitchEq ord (fun j _ ↦ (clocks j).1) (fun j _ ↦ (clocks j).2)
  refine ⟨ps,hgroup,hids,hrs,?_⟩
  rw [SourceOnline.post,hrs]
  exact complete.remainder.sweep.replay

end Physical
end CompressorRecords.SurvivingPackets

end

end VPVNP
end Computability
end OAI
