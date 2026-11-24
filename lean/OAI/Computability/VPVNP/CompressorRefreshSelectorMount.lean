import OAI.Computability.VPVNP.CompressorRefreshSourceWorker
import OAI.Computability.VPVNP.CompressorRefreshBeforeGroup

/-! # Mounting a refresh selector from its deterministic preparation

Every live scheduler boundary agreeing with the generated data suffix can
install the actual term selector. Its level header and planner pitch are
retained by the same refresh prefix that produces its demand coordinates.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace CompressorRecords.RefreshSelector

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh PairSimulation.LocalHistory
open PortRefresh PortRefresh.LevelRecipe PortRefresh.Allocation SelectedTerms NewSlots BlockPlanner DescriptorSpace
open Schedule PhaseRecipe SourceTransport ScheduledTrace SourceOnline
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
variable {g w : ℕ} (pub : Fin 11 → BurstRAM.Word w) (positions blocks t : ℕ)
variable (X : State S.portExponent (S.portExponent+g))
local notation "O" => PassOrigin.refresh (B := B) (f := f) (hf := hf) X
local notation "sh" => RefreshBlockPlan.shape B
local notation "d" => LevelRecipe.Shape.ties sh
local notation "stride" => LevelRecipe.Shape.stride sh
local notation "e" => (LevelRecipe.Shape.ports sh)*(LevelRecipe.Shape.dH sh)
local notation "scr" => BlockProgram.script B
local notation "base" => pub 2
local notation "layout" => BlockProgram.layout B (Fin.val base) positions blocks
local notation "firstLevel" => Script.levelsPerBlock scr*t
local notation "cur" => firstLevel+S.steps
local notation "start" => arrayBase layout cur
local notation "old" => packedIncidence layout w cur ((State.positions X)*2^S.portExponent)
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "atRow" => List.length (Script.initial scr)+t*List.length (Script.block scr)+Fin.val (Window.position (selectorWindow B) 0)
local notation "H" => levelStart layout 0
local notation "tag" => LiveStageLink.tagWord w (Online.calendarIndex (Script.size scr) (Script.size scr))
local notation "inp" => RefreshBlockPlan.input (BlockProgram.geometry B) S.steps (0 : Fin 6)

/-- The prepared post-memory contains the selector's physical inputs. Any
matching live calendar at this ordinal installs that selector, before any
term tape or any succeeding level is chosen. -/
private theorem mount (termCap small cap : ℕ) (m : Memory w) (rs : List (Report w))
    (pre : RefreshPrepare.Prepared B base positions blocks t X m rs)
    (ht : t<blocks) (size : X.positions ≤ positions) (fit : endAddress layout < 2^w)
    (rows : after m (eventLog rs) (pt).rows.val = (directoryRows layout : BurstRAM.Word w))
    (pitch : after m (eventLog rs) ((pt).directory-1).val = (levelWords layout : BurstRAM.Word w))
    (header : RefreshCore.Header (Fintype.card X.Base) g (levelStart layout cur) start old (after m (eventLog rs)))
    (width : SelectedTermWorker.fitConstant B+4*Nat.clog 2 (X.maxWireWidth+1) ≤ w)
    (fuel : TermWorker.budget B.refresh d e w X.maxWireWidth ≤ termCap)
    (scanClock : scanCap scr (max 64 termCap) ≤ small) (runtime : small ≤ cap) :
    ∀ mid : Memory w, Agree (H ≤ ·) (after m (eventLog rs)) mid → mid (pt).tag.val = tag →
      (mid (pt).ordinal.val).val = atRow → (mid (pt).rows.val).val = directoryRows layout →
      mid ((pt).directory-1).val = (levelWords layout : BurstRAM.Word w) → Nonempty (SelectorSite O layout pub cap small mid) := by
  let raw := after m (eventLog rs)
  have idx : cur < (layout).levels := by
    have bound := Nat.mul_le_mul_left (S.steps+1) ht
    rw [Nat.mul_succ] at bound
    change (S.steps+1)*t+S.steps < 1+(S.steps+1)*blocks
    omega
  let current : Fin (layout).levels := ⟨cur,idx⟩
  have src := RefreshCore.source_region B base positions blocks t X current rfl size fit
  have room := (BlockLevelFit.refresh B (base).val positions blocks current rfl X size fit).1.word
  change (plan X (S.degreeExponent 0) (sh).dH d stride (start+0*tableWords layout)).stop < 2^w at room
  simp only [Nat.zero_mul,Nat.add_zero] at room
  let alloc := prepare_layout X old (S.degreeExponent 0) (sh).dH d stride start (fun j ↦ (src j).2) room
  have Hfit := (levelStart_mono layout (Nat.zero_le _)).trans_lt fit
  have before : levelStart layout cur+60 < start := by
    change levelStart layout cur+60 < levelStart layout cur+66+6*slotCapacity layout
    omega
  have low : H ≤ start := (levelStart_mono layout (Nat.zero_le cur)).trans ((Nat.le_add_right ..).trans before.le)
  let C : Context w := ⟨(pt).data,(levelStart layout firstLevel : BurstRAM.Word w),raw⟩
  have entry : LevelFields.Entry layout firstLevel C.pub C.state C.memory := ⟨rfl,pitch⟩
  have describes : Describes (s := sh) inp C X start old := RefreshCore.Header.describes
    (F := BlockProgram.geometry B) (s := sh) (X := X) (step := S.steps) rfl (0 : Fin 6) rfl entry header
  have live : atRow < directoryRows layout := by
    rw [BlockProgram.directory_rows,(scr).calendar_total]
    have j := ((selectorWindow B).position 0).isLt
    have bound := Nat.mul_le_mul_right (scr).block.length ht
    rw [Nat.succ_mul] at bound
    omega
  let pkt := packet B C termCap [] []
  have worker := sourceWorker B f hf X old start layout C describes alloc low room width termCap fuel pre.demands [] []
  have preparedPacket := prepared B X old start layout base t raw termCap [] [] rfl rfl Hfit rows pitch live header
  have costs := scanCap_clocks (A := scr) (p := pkt) (max 64 termCap) (Nat.le_max_right ..) scanClock
  intro mid same htag hord hrows hstride
  exact ⟨SelectorSite.ofPrepared (B := B) (L := layout) (pub := pub) _ pkt worker preparedPacket
    costs.1 costs.2 runtime rfl rfl Hfit live le_rfl same htag hord hrows hstride⟩

/-- The header and preparation occupy exactly the ordinals preceding the fixed
term worker in a full repeated block. -/
theorem before_offset {small : ℕ} {m : Memory w} {hs ds : List (SourceOnline.Packet scr w)}
    (h : RefreshBefore.Before B f hf base positions blocks t X small m hs ds) :
    (RefreshHeaders.window B).before.length+(hs++ds).length = (BlockIndex.blockRefresh B).index.val := by
  have counts := congrArg List.length h.phases
  simp only [List.length_map,List.length_append,Window.indices,List.length_ofFn] at counts
  have headers : (RefreshHeaders.window B).before.length = ((List.finRange S.steps).flatMap (BlockProgram.shrink B)).length := by
    change (BlockGroups.refresh B 0).before.length = _
    rw [BlockGroups.refresh_offset]
    rfl
  have dataLen : (RefreshPrepare.stages B).length = 3+(sh).ties := by
    simp [RefreshPrepare.stages]; omega
  have hk : hs.length+ds.length = 3+(RefreshPrepare.stages B).length := by
    simpa only [BlockHeaderPlan.substep_length] using counts
  rw [headers,BlockIndex.block_refresh_offset,List.length_append,hk,dataLen]
  omega

/-- The choice-independent header and demand packets install the actual selector at
its ordinal in the repeated full block, on every matching live scheduler memory. -/
theorem mountBefore (termCap small cap : ℕ) (m : Memory w) (hs ds : List (SourceOnline.Packet scr w))
    (h : RefreshBefore.Before B f hf base positions blocks t X small m hs ds)
    (ht : t<blocks) (size : X.positions ≤ positions) (fit : endAddress layout < 2^w)
    (width : SelectedTermWorker.fitConstant B+4*Nat.clog 2 (X.maxWireWidth+1) ≤ w)
    (fuel : TermWorker.budget B.refresh d e w X.maxWireWidth ≤ termCap)
    (scanClock : scanCap scr (max 64 termCap) ≤ small) (runtime : small ≤ cap) :
    ∀ mid : Memory w, Agree (H ≤ ·) (post m (hs++ds)) mid → mid (pt).tag.val = tag →
      (mid (pt).ordinal.val).val = (scr).initial.length+t*(scr).block.length+(BlockIndex.blockRefresh B).index.val →
      (mid (pt).rows.val).val = directoryRows layout → mid ((pt).directory-1).val = (levelWords layout : BurstRAM.Word w) →
      Nonempty (SelectorSite O layout pub cap small mid) := by
  let mid := post m hs
  let rs := ds.flatMap SourceWalk.Packet.reports
  have eqn : post m (hs++ds) = after mid (eventLog rs) := post_append ..
  rw [eqn,← selector_position B]
  exact mount B f hf pub positions blocks t X termCap small cap mid rs h.data ht size fit
    (eqn ▸ h.rows) (eqn ▸ h.pitch) (eqn ▸ h.header) width fuel scanClock runtime

end CompressorRecords.RefreshSelector

end

end VPVNP
end Computability
end OAI
