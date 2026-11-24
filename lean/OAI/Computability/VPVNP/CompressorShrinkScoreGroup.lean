import OAI.Computability.VPVNP.CompressorShrinkScoreOperands
import OAI.Computability.VPVNP.CompressorShrinkTermOnline
import OAI.Computability.VPVNP.CompressorPublishedHeadWindows

/-! # The score packet group in the complete repeated block program

At the 22nd offset of each shrinking substep the actual ten visits clear both
accumulators, read the eight selected coordinates and publish the chosen bit.
The reports leave the same post-memory as the verified selected score run.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ScorePackets

open BurstRAM Compression BlockPlanner ShrinkBlockInputs DescriptorSpace SourceTransport PhaseRecipe Schedule
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
local notation "script₀" => BlockProgram.script B
local notation "O" => BlockProgram.arena B i.val 0
local notation "I" => selectedInputs B (BlockProgram.geometry B) i (BlockProgram.arena B i.val 0)

/-- Locates the ten score visits in the repeated block, directly after the term-record visits
and before placement uses the selected layout. -/
def window : Window script₀ (visits I) where
  before := (ShrinkTermOnline.window B i).before ++ termVisits B i O
  after := [SelectedPlan.placement I,SelectedPlan.roles I,SelectedPlan.clearChildren I,SelectedPlan.children I (a i)] ++
    (BlockProgram.shrink B i).drop (beforeSlices B (BlockProgram.geometry B) i O).length ++ BlockIndex.later B i
  block := by
    rw [(ShrinkTermOnline.window B i).block,visits_eq]
    simp only [ShrinkTermOnline.window,ShrinkTermOnline.remaining,SelectedPlan.visits,
      List.append_assoc,List.cons_append,List.nil_append]

theorem before_length : (window B i).before.length = (BlockIndex.earlier B i).length+22 := by
  change ((BlockIndex.earlier B i ++ ShrinkTermOnline.prior B i) ++ termVisits B i O).length = _
  rw [List.length_append,List.length_append,ShrinkTermOnline.prior_length,termVisits_length]

variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (T : IncidenceDirectory w) (start : ℕ)
variable (base : Word w) (positions blocks t : ℕ)
local notation "W" => window B i
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog script₀)) base
local notation "pub" => Schedule.Ports.data pt
local notation "first₀" => Script.levelsPerBlock script₀ * t
local notation "st" => (levelStart L (first₀) : Word w)
local notation "D" => Window.operandRegion script₀ L base
local notation "H" => levelStart L 0
local notation "head" => levelStart L (first₀+i.val)
local notation "term" => ShrinkInput.termHead (w := w) X start
local notation "table" => SelectedArena.scoreTables X term (10 : Word w) (B.shrink.selectorBits : Word w)
local notation "N" => SelectedArena.motifs X
local notation "Pkt" => SourceWalk.Packet (SourceOnline.Visit script₀ w) w

private theorem paths {tab : TermScores.Tables w} {n : ℕ} {js : List Stage} {m : Memory w} {rs : List (Report w)}
    (h : SourceWalk (Native tab n) js m rs) :
    branchPaths rs = List.replicate ((js.map (Stage.limit n)).sum) [] := by
  induction h with
  | done => rfl
  | @next j js m xs ys hs _ ih =>
    have eq : branchPaths xs = List.replicate (j.limit n) [] := by
      cases j with
      | axis j => exact ((runSegment_iff ..).mp hs).2.2
      | clear => subst xs; rfl
      | compare => subst xs; rfl
    rw [branchPaths,List.map_append,← branchPaths,← branchPaths,eq,ih,List.map_cons,List.sum_cons,List.replicate_add]

set_option maxHeartbeats 1200000 in
private theorem raw {js : List Stage} {mem : Memory w} {rs : List (Report w)}
    (run : SourceWalk (Native table N) js mem rs)
    (region : Region table N)
    (room : ShrinkInput.termEnd X start 10 < 2^w) (before : head+60 < start)
    (fit : H < 2^w) (header : ShrinkHeaderReads.Header i X T start L (first₀) mem)
    (pitch : mem (pub 1-1).val = (levelWords L : Word w)) :
    SourceWalk (Window.Raw (A:=script₀) L base t 27) (js.map (Stage.visit I)) mem rs := by
  have low : H ≤ head := levelStart_mono L (Nat.zero_le _)
  have lower := start_le_term i X start room
  have control := Window.lowCells (A:=script₀) L base rfl rfl fit
  induction run with
  | done => exact .done _
  | @next j js m xs ys hs _ ih =>
    have entry : LevelFields.Entry L (first₀) pub st m := ⟨rfl,pitch⟩
    have ev := term_values B i X T start pub st m (header.reads B entry) room
    have sup := term_support B i X T start pub st m header entry D (Or.inr (.inl rfl))
      (fun z _ => Or.inr (.inr (low.trans (Nat.le_add_right ..))))
    have score : (SelectedPlan.scoreBase I).eval pub st m = (table).scoreBase := by
      change (I).termBase.eval pub st m + (I).motifs.eval pub st m * (10 : Word w) = _
      rw [ev.1,ev.2]
      have tr : ((term).val : Word w) = term := Fin.ext (Nat.mod_eq_of_lt (term).isLt)
      have ten : 10 < 2^w := by
        have h := region.one
        have h₀ := header.room; omega
      change _ = (((term).val + N*(10 : Word w).val : ℕ) : Word w)
      have hten : (10 : Word w).val = 10 := Nat.mod_eq_of_lt ten
      rw [hten,Nat.cast_add,Nat.cast_mul,tr,Nat.cast_ofNat]
    have cell : (SelectedPlan.layoutCell I).eval pub st m = (table).levelCell := by
      change (SelectedPlan.scoreBase I).eval pub st m + 2 = _
      rw [score]
      change ((_ : ℕ) : Word w)+2 = ((_+2 : ℕ) : Word w)
      rw [Nat.cast_add,Nat.cast_ofNat]
    have values : Readback I pub st m table N := ⟨ev.2,ev.1,rfl,rfl,score,cell⟩
    have packet := hs.run I pub st m table N L (by change H ≤ (term).val; omega) region values j xs
    have bounds := hs.bounds table N region j m xs
    have keep (x : ℕ) (hx : x < start) : after m (eventLog xs) x = m x :=
      after_outside m bounds.2.2 (show ¬(term).val ≤ x by omega)
    have gap : (pub 1-1).val < start := by
      have h : (pub 1-1).val < H := control.2
      omega
    exact .next ⟨j.fuel,List.replicate (j.limit N) [],j.fuel_le,packet,supported I pub st m D j sup.2 sup.1⟩
      (ih (header.keep_below before keep) ((keep _ gap).trans pitch))

set_option maxHeartbeats 1800000 in
/-- Install all ten score visits at the true shrinking substep, from the
executed score run in the selected branch. The group has its exact post-memory
and one empty choice stream per actual worker call. -/
theorem group (cap : ℕ) (mem : Memory w) (scores : List (Report w))
    (execute : TermScores.run table N (List.ofFn SelectedScore.axes) mem = some scores)
    (live : t < blocks) (room : ShrinkInput.termEnd X start 10 < 2^w) (before : head+60 < start)
    (selectedFit : SelectedArena.Fits X term (10 : Word w))
    (header : ShrinkHeaderReads.Header i X T start L (first₀) mem)
    (rows : mem (pt).rows.val = (directoryRows L : Word w)) (pitch : mem (pub 1-1).val = (levelWords L : Word w))
    (clock : SourceOnline.scanCap script₀ 27 ≤ cap) :
    ∃ ps : List Pkt, SourceOnline.Group script₀ L base cap ((script₀).initial.length+t*(script₀).block.length+
        (BlockIndex.earlier B i).length+22) (directoryRows L) mem ps ∧
      ps.map (fun p => p.stage.phase) = (W).indices ∧
      eventLog (ps.flatMap SourceWalk.Packet.reports) = eventLog scores ∧
      ps.flatMap (fun p => p.stage.choices) = List.replicate (8*N+2) [] := by
  obtain ⟨logs,hs,events⟩ := walk table N mem scores execute
  have low := levelStart_mono L (Nat.zero_le (first₀+i.val))
  have hroom := header.room
  have ten : 10 < 2^w := by omega
  have region := Region.selected X term (10 : Word w) (B.shrink.selectorBits : Word w)
    (show 10 ≤ (10 : Word w).val by change 10 ≤ 10%(2^w); rw [Nat.mod_eq_of_lt ten]) selectedFit
  have hi : H < 2^w := by omega
  have hrs := raw B i X T start base positions blocks t hs region room before hi header pitch
  have clocks (j : Fin (script₀).size) :
      ((script₀).plan.recipes j).2.code.length+1+2*Online.N (script₀).size (script₀).size+5 ≤ cap ∧
      27+3+4*(((script₀).catalog j).params+1)+2*Online.N (script₀).size (script₀).size+5 ≤ cap :=
    SourceOnline.scanCap_clocks (p:=⟨HeaderPacket.attach script₀ j pub st mem 27 [],mem,[]⟩) 27 le_rfl clock
  obtain ⟨ps,gp,ids,logEq⟩ := (W).group L base t rfl rfl hi cap 27 mem logs hrs rows pitch
    (PublishedHeads.windowLive B base positions blocks t W live) (fun j _ => (clocks j).1) (fun j _ => (clocks j).2)
  refine ⟨ps,?_,ids,(congrArg eventLog logEq).trans events,?_⟩
  · rw [before_length,Nat.add_assoc] at gp
    convert gp using 1; omega
  · rw [PublishedHeads.chronological_tapes mem ps gp.chronological,logEq,paths hs]
    congr 1
    simp [stages,Stage.limit]; omega

end CompressorRecords.ScorePackets

end

end VPVNP
end Computability
end OAI
