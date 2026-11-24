import OAI.Computability.VPVNP.CompressorShrinkSelectedReadback
import OAI.Computability.VPVNP.CompressorBlockGroups
import OAI.Computability.VPVNP.CompressorWindowPackets
import OAI.Computability.VPVNP.CompressorSourceScanned

/-! # Installing the four selected shrinking scans in the global block -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.SelectedTailPackets

open BurstRAM Compression BlockPlanner DescriptorSpace Schedule SourceTransport ShrinkBlockInputs SelectedArena
open scoped Fin.CommRing Classical

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
local notation "script₀" => BlockProgram.script B
local notation "I" => selectedInputs B (BlockProgram.geometry B) i (BlockProgram.arena B i.val 0)

/-- Locates the four placement, role, and child-directory visits immediately after the ten
scoring visits in the repeated shrink block. -/
def window : Window script₀ (tail I (a i)) where
  before := (BlockGroups.shrink B i 4).before ++
    ([SelectedPlan.clear I]++List.ofFn (SelectedPlan.axis I)++[SelectedPlan.compare I])
  after := (BlockGroups.shrink B i 4).after
  block := by
    let W : Window script₀ (SelectedPlan.visits I (a i)) := BlockGroups.shrink B i 4
    exact W.block.trans ((congrArg (fun ls => W.before ++ ls ++ W.after) (split (a:=a i) I)).trans (by simp only [List.append_assoc]; rfl))

theorem window_offset : (window B i).before.length = (BlockIndex.earlier B i).length+32 := by
  change ((BlockGroups.shrink B i 4).before++_).length=_
  rw [List.length_append,BlockGroups.shrink_offset]
  change (BlockIndex.earlier B i).length+
    ((BlockHeaderPlan.substep _ _ _ ++ (GreedyLevelPlan.visits _ _ _ _ ++
      (ShrinkBundlePlan.visits _ _ _ _ ++ (termVisits B i _ ++ [])))).length)+_ = _
  simp only [List.length_append,BlockHeaderPlan.substep_length,GreedyLevelPlan.visits_length,
    ShrinkBundlePlan.visits_length,termVisits_length,List.length_nil,List.length_cons,List.length_ofFn]

variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (T : IncidenceDirectory w) (start : ℕ)
variable (base : Word w) (positions blocks t : ℕ)
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (BlockPlanner.Script.catalog (BlockProgram.script B))) base
local notation "pub" => Schedule.Ports.data pt
local notation "first" => BlockPlanner.Script.levelsPerBlock (BlockProgram.script B)*t
local notation "st" => (levelStart L (first) : Word w)
local notation "H" => levelStart L 0
local notation "D" => Window.operandRegion script₀ L base
local notation "term" => ShrinkInput.termHead (w := w) X start
local notation "p₀" => ShrinkInput.placementBank X T start
local notation "W" => window B i
local notation "low" => levelStart L (first+i.val)


open private room_vals from OAI.Computability.VPVNP.CompressorRecordsSelectedPreimages

set_option maxHeartbeats 1800000 in
theorem group (s : SelectedScore.Selection B X) (m : Memory w) (p : SelectedStage.Passes w) (q : SelectedFinish.Passes w)
    (exec : SelectedStage.Execution X term 10 (B.shrink.selectorBits : Word w) p₀ T m p)
    (stored : SelectedStage.Stored B X term 10 p₀ s m p)
    (built : SelectedFinish.Built B X term 10 (B.shrink.selectorBits : Word w) p₀ s m p q)
    (hp : ShrinkRAM.Params p₀ (a i) (Shrink.colors (a i)) (Shrink.J (a i)) g false)
    (old : OldInputs X term 10 p₀ T) (termRoom : ShrinkInput.termEnd X start 10 < 2^w)
    (room : SelectedFinish.stop X term 10 ≤ 2^w)
    (header : ShrinkHeaderReads.Header i X T start L (first) (p.afterScores m)) (before : low+60 < start)
    (floor : H ≤ ShrinkHistoryTrace.inputFloor p₀) (outFloor : H≤T.actualOut.val)
    (rows : p.afterScores m (pt).rows.val=(directoryRows L : Word w))
    (pitch : p.afterScores m (pub 1-1).val=(levelWords L : Word w))
    (within : t<blocks) (fit : endAddress L<2^w) (cap : ℕ) (clock : SourceOnline.scanCap script₀ 65≤cap) :
    ∃ ps : List (SourceOnline.Packet script₀ w), SourceOnline.Group script₀ L base cap
      ((script₀).initial.length+t*(script₀).block.length+(BlockIndex.earlier B i).length+32) (directoryRows L) (p.afterScores m) ps ∧
      ps.map (fun r => r.stage.phase) = (W).indices ∧ ps.flatMap SourceWalk.Packet.reports = reports p q ∧
      SourceOnline.post (p.afterScores m) ps=q.final (p.final m) := by
  have baseFit : H < 2^w := (levelStart_mono L (Nat.zero_le _)).trans_lt fit
  have lowBound : H≤low := levelStart_mono L (Nat.zero_le _)
  have hh := Window.lowCells (A:=script₀) L base rfl rfl baseFit
  have termLow := ScorePackets.start_le_term i X start termRoom
  have size : 10<2^w := by have := header.room; omega
  obtain ⟨full,cval,_⟩ := room_vals X term (10 : Word w) room
  obtain ⟨_,wp,_,wr⟩ := ShrinkHistoryTrace.selected_access B X term (10 : Word w) (B.shrink.selectorBits : Word w)
    p₀ T s m p exec stored old hp full
  have pl : start≤placementBase X term (10 : Word w) := termLow.trans (by
    change (term).val ≤ (term).val + _ + 3; omega)
  have rl : start≤roleBase X term (10 : Word w) := pl.trans (Nat.le_add_right ..)
  have posKeep (x : ℕ) (hx : x<start) : p.afterPositions m x=p.afterScores m x :=
    after_outside _ wp (fun h => Nat.not_le_of_lt (hx.trans_le pl) h.1)
  have roleKeep (x : ℕ) (hx : x<start) : p.final m x=p.afterScores m x :=
    (after_outside _ wr (fun h => Nat.not_le_of_lt (hx.trans_le rl) h.1)).trans (posKeep x hx)
  let area := SelectedFinish.areas X term 10 p₀ (p.afterScores m (origin X term 10+2)) room
  obtain ⟨_,_,wc⟩ := ShrinkHistoryTrace.clear_scanned _ _ (area.countEnd.trans (SelectedFinish.rows X term 10).isLt.le)
    _ _ built.raw.clear
  have countBound : start≤(SelectedFinish.counts X term 10).val := cval.symm ▸ (rl.trans (Nat.le_add_right ..))
  have clearKeep (x : ℕ) (hx : x<start) : q.middle (p.final m) x=p.afterScores m x :=
    (after_outside _ wc (fun h => Nat.not_le_of_lt (hx.trans_le countBound) h.1)).trans (roleKeep x hx)
  have source (r : Memory w) (hr : r∈inputs m p q) :
      SelectedPlan.Reads I X p₀ T term pub st r ∧ Footprint I D pub st r := by
    have same (x : ℕ) (hx : x<start) : r x=p.afterScores m x := by
      simp only [inputs,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl
      · rfl
      · exact posKeep x hx
      · exact roleKeep x hx
      · exact clearKeep x hx
    have entry : LevelFields.Entry L (first) pub st r := ⟨rfl,(same _ (hh.2.trans (lowBound.trans_lt (by omega)))).trans pitch⟩
    exact header_values B i X T start pub st r (header.keep_below before same) entry termRoom size D
      (.inr (.inl rfl)) (fun n _ => .inr (.inr (lowBound.trans (Nat.le_add_right ..))))
  have walk := SelectedTailPackets.walk I X term p₀ T D pub st L B s m p q exec stored built hp old room
    floor outFloor (lowBound.trans ((show low≤start by omega).trans termLow)) (fun _ h => Or.inr (Or.inr h)) source
  have budget (j : Fin (script₀).size) :
      ((script₀).plan.recipes j).2.code.length+1+2*Online.N (script₀).size (script₀).size+5≤cap ∧
      65+3+4*(((script₀).catalog j).params+1)+2*Online.N (script₀).size (script₀).size+5≤cap := by
    let e := HeaderPacket.attach script₀ j pub st m 65 []
    exact SourceOnline.scanCap_clocks (p:=⟨e,m,[]⟩) 65 (by rfl) clock
  have live (j : Fin (tail I (a i)).length) : Window.ordinal (A:=script₀) t ((W).index j)<directoryRows L := by
    rw [(W).ordinal_index,BlockProgram.directory_rows,(script₀).calendar_total]
    have pos := ((W).position j).isLt
    have gt := Nat.mul_le_mul_right (script₀).block.length within
    rw [Nat.succ_mul] at gt
    omega
  obtain ⟨ps,hg,ph,rep⟩ := (W).group L base t rfl rfl baseFit cap 65 _ _ walk rows pitch live
    (fun j _ => (budget j).1) (fun j _ => (budget j).2)
  rw [window_offset] at hg
  refine ⟨ps,?_,ph,rep,?_⟩
  · simpa only [Nat.add_assoc] using hg
  · rw [SourceOnline.post,rep,reports,SourceWalk.after_append,SourceWalk.after_append,SourceWalk.after_append]
    rfl

end CompressorRecords.SelectedTailPackets

end

end VPVNP
end Computability
end OAI
