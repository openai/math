import OAI.Computability.VPVNP.CompressorShrinkABSliceWindow
import OAI.Computability.VPVNP.CompressorWindowPackets
import OAI.Computability.VPVNP.CompressorGreedyPlannerFootprint
import OAI.Computability.VPVNP.CompressorSourceScanned

/-!
# Checked and prepared AB packets at their actual block ordinals

At each repeated block, the AB window starts after the selected term and
resident directory visits. Its public words read the pitch and six header
cells of the current shrinking level. The online script therefore launches
the actual fixed workers in every live memory that agrees on the persistent
data, with the exact bounds and native reports of the shrinking construction.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.BlockSlices

open BurstRAM PhaseRecipe BlockPlanner Compression ShrinkBlockInputs DescriptorSpace SourceTransport
open ShrinkABSliceRecipe Schedule
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {w : ℕ} (base : Word w) (pos blocks round : ℕ)
local notation "scr" => BlockProgram.script B
local notation "F" => BlockProgram.geometry B
local notation "O" => BlockProgram.arena B i.val 0
local notation "AB" => BlockProgram.arena B i.val 1
local notation "I" => abInputs i O AB
local notation "L" => BlockProgram.layout B base.val pos blocks
local notation "pt" => Workspace.ports (arity (Script.catalog (BlockProgram.script B))) base
local notation "pub" => Ports.data pt
local notation "blockStart" => (S.steps+1)*round
local notation "cur" => blockStart+i.val
local notation "s" => ((levelStart L blockStart : ℕ) : Word w)
local notation "origin" => tableBase L cur (0 : Fin 6)
local notation "first" => tableBase L cur (1 : Fin 6)
local notation "H" => levelStart L 0
local notation "D" => Window.operandRegion scr L base
local notation "W" => abWindow B i

private theorem weaken_walk {J : Type*} {src dest : J → Memory w → List (Report w) → Prop}
    (f : ∀ j mem rs, src j mem rs → dest j mem rs) {js : List J} {mem : Memory w} {rs : List (Report w)}
    (walk : SourceWalk src js mem rs) : SourceWalk dest js mem rs := by
  induction walk with
  | done => exact .done _
  | next head _ ih => exact .next (f _ _ _ head) ih

private theorem header_support (m : Memory w) (entry : LevelFields.Entry L blockStart pub s m)
    (active : cur < (L).levels) (fit : endAddress L < 2^w) :
    Supported (fun x => D x ∧ x < origin) pub s m I := by
  have hg : arity (scr).catalog = (L).shape.arity := rfl
  have hb : base.val = (L).base := rfl
  have hH := (levelStart_mono L (Nat.zero_le (L).levels)).trans_lt fit
  have gap := (Window.lowCells (A := scr) L base hg hb hH).2
  have low := levelStart_mono L (Nat.zero_le cur)
  have earlier : incidenceStart L cur ≤ origin := by
    change incidenceStart L cur ≤ incidenceStart L cur+_+_
    omega
  have after : incidenceStart L cur ≤ levelStart L (cur+1) :=
    (earlier.trans (Nat.le_add_right origin (tableWords L))).trans (tableEnd_le_nextLevel L cur (0 : Fin 6))
  have bound := (after.trans (levelStart_mono L active)).trans_lt fit
  have pitch : D (pub 1-1).val ∧ (pub 1-1).val < origin := ⟨Or.inr (Or.inl rfl),
    gap.trans_le (low.trans ((Nat.le_add_right (levelStart L cur) (levelHeaderWords L)).trans earlier))⟩
  have scalar (off : ℕ) (small : off < 62) :
      (LevelFields.scalar i.val off).ReadsFrom (fun x => D x ∧ x < origin) pub s m := by
    have inside : levelStart L cur+off < incidenceStart L cur := by
      change levelStart L cur+off < levelStart L cur+66
      omega
    exact GreedyVisit.scalar_support _ L blockStart i.val off entry pitch
      ⟨Or.inr (Or.inr (low.trans (Nat.le_add_right ..))),inside.trans_le earlier⟩ (inside.trans bound)
  exact ab_supported i _ pub s m O AB (fun j => scalar j.val (by have := j.isLt; omega))
    (scalar 60 (by decide)) (scalar 61 (by decide))

private theorem clocks (cap : ℕ) (hc : SourceOnline.scanCap scr 95 ≤ cap) (j : Fin (scr).size) :
    ((scr).plan.recipes j).2.code.length+1+2*Online.N (scr).size (scr).size+5 ≤ cap ∧
      95+3+4*(((scr).catalog j).params+1)+2*Online.N (scr).size (scr).size+5 ≤ cap := by
  have rc := Finset.le_sup (f := fun j : Fin (scr).size => ((scr).plan.recipes j).2.code.length+1+2*Online.N (scr).size (scr).size+5)
    (Finset.mem_univ j)
  have ar := params_le_arity (scr).catalog j
  unfold SourceOnline.scanCap at hc
  exact ⟨rc.trans ((le_max_left ..).trans hc),(by omega)⟩

set_option maxHeartbeats 900000 in
/-- At the physical AB stage of the live compiled script the stored guard
and interval trace give complete source packets and their actual launches. -/
theorem ab_packets (rows high : ℕ) (t p : Fin 5 → Word w) (m : Memory w) (rs : List (Report w))
    (hblock : round < blocks) (active : cur < (L).levels) (fit : endAddress L < 2^w)
    (total : m (pt).rows.val = (directoryRows L : Word w))
    (pitch : m ((pt).directory-1).val = (levelWords L : Word w))
    (heads : Describes I pub s m t p rows first)
    (walk : SourceWalk (Guarded I pub s m rows 95 (fun x => origin ≤ x ∧ x < high))
      (phases (ShrinkBundlePlan.thickCount (a i)) (ShrinkBundlePlan.cap (a i))) m rs)
    (cap : ℕ) (capFit : SourceOnline.scanCap scr 95 ≤ cap) :
    ∃ ps : List (SourceOnline.Packet scr w),
      SourceOnline.Group scr L base cap ((scr).initial.length+round*(scr).block.length+(W).before.length)
        (directoryRows L) m ps ∧ ps.map (fun p => p.stage.phase)=(W).indices ∧
      ps.flatMap SourceWalk.Packet.reports=rs := by
  have entry : LevelFields.Entry L blockStart pub s m := ⟨rfl,pitch⟩
  have low : H ≤ origin := (levelStart_mono L (Nat.zero_le cur)).trans (by
    change levelStart L cur ≤ levelStart L cur+_+_+_; omega)
  have supported := header_support B i base pos blocks round m entry active fit
  have native := ab_header_walk I L D origin high t p heads low supported _ m rs walk (fun _ _ => rfl)
  have raw : SourceWalk (Window.Raw (A := scr) L base round 95) (intersections i O AB) m rs := by
    change SourceWalk _ (List.map (stage I) _) _ _
    exact weaken_walk (fun _ _ _ head => ⟨95,_,le_rfl,head.1,head.2⟩) native
  have live (j : Fin (intersections i O AB).length) :
      Window.ordinal (A:=scr) round ((W).index j) < directoryRows L := by
    rw [Window.ordinal_index,BlockProgram.directory_rows,(scr).calendar_total]
    have step := Nat.mul_le_mul_right (scr).block.length hblock
    rw [Nat.succ_mul] at step
    have loc := ((W).position j).isLt
    omega
  exact (W).group L base round rfl rfl ((levelStart_mono L (Nat.zero_le (L).levels)).trans_lt fit) cap 95 m rs raw
    total pitch live (fun j _ => (clocks B cap capFit j).1) (fun j _ => (clocks B cap capFit j).2)

end CompressorRecords.BlockSlices

end

end VPVNP
end Computability
end OAI
