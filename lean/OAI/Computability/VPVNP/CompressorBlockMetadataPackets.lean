import OAI.Computability.VPVNP.CompressorBlockMetadata
import OAI.Computability.VPVNP.CompressorBlockGroups
import OAI.Computability.VPVNP.CompressorWindowPackets
import OAI.Computability.VPVNP.CompressorSourceScanned

/-! # Native online packets for the three DFS metadata publications -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BlockMetadata

open BurstRAM DescriptorSpace PhaseRecipe BlockPlanner Schedule SourceTransport SourceOnline
open scoped Fin.CommRing

variable {w : ℕ}

/-- Each source segment inherits the event footprint of its chronological
walk. The same footprint preserves the lower control words at every join. -/
private theorem data_walk {J : Type*} {src dest : J → Memory w → List (Report w) → Prop}
    {js : List J} {m : Memory w} {rs : List (Report w)}
    (h : SourceWalk src js m rs) (head : ℕ) (original : Memory w)
    (agree : ∀ x < head, m x = original x)
    (rd : Reads (head ≤ ·) (eventLog rs)) (wr : Writes (head ≤ ·) (eventLog rs))
    (lift : ∀ j ∈ js, ∀ mem logs, src j mem logs → (∀ x < head, mem x = original x) →
      Reads (head ≤ ·) (eventLog logs) → Writes (head ≤ ·) (eventLog logs) → dest j mem logs) :
    SourceWalk dest js m rs := by
  induction h with
  | done => exact .done _
  | @next j js m xs ys srcHead _ ih =>
    rw [eventLog,List.flatMap_append] at rd wr
    have rd₁ : Reads (head ≤ ·) (eventLog xs) := fun a v hv => rd a v (List.mem_append_left _ hv)
    have wr₁ : Writes (head ≤ ·) (eventLog xs) := fun a v hv => wr a v (List.mem_append_left _ hv)
    have middle (x) (hx : x<head) : after m (eventLog xs) x = original x :=
      (after_outside m wr₁ (Nat.not_le_of_lt hx)).trans (agree x hx)
    exact .next (lift j List.mem_cons_self m xs srcHead agree rd₁ wr₁)
      (ih middle (fun a v hv => rd a v (List.mem_append_right _ hv))
        (fun a v hv => wr a v (List.mem_append_right _ hv))
        (fun k hk => lift k (List.mem_cons_of_mem _ hk)))

private theorem limits (F : Shape) (step limit deg : ℕ) (role : Role) (v : Fields)
    (pub : Fin 5 → Word w) (st : Word w) (m : Memory w) :
    ∀ j ∈ visits F step limit deg role v, j.initial.eval pub st m = 0 ∧ j.stop.eval pub st m = 1 := by
  intro j hj
  simp only [visits,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl | rfl <;> exact ⟨Nat.cast_zero,Nat.cast_one⟩

variable {k : Type*} [_root_.Field k] {S : Compression.BlockSchedule k} (B : S.Templates)
variable (base : Word w) (positions blocks t step : ℕ) (role : Role) (fields : Fields)
local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "pub" => Schedule.Ports.data pt
local notation "first" => Script.levelsPerBlock scr*t
local notation "st" => (levelStart L (first) : Word w)
local notation "head" => levelStart L (first+step)
local notation "nextHead" => levelStart L (first+(step+1))
local notation "vis" => visits (Layout.shape L) step B.recordLimit (slotDegree S) role fields
local notation "D" => Window.operandRegion scr L base
local notation "Pkt" => SourceOnline.Packet scr w

/-- All twelve descriptor fields, the next DFS row pointer and the role
are read from the actual post-memory. Writes outside these fourteen cells
are excluded on the complete chronological report stream. -/
structure Published (m : Memory w) (oldSites : ℕ) (rs : List (Report w)) : Prop where
  payload : ∀ j : Fin 12, after m (eventLog rs) (head+15+j.val) =
    (fieldExprs (L).shape step B.recordLimit (slotDegree S) fields j).eval pub st m
  successor : after m (eventLog rs) (nextHead+14) =
    m (head+14)+((B.recordLimit+2 : ℕ) : Word w)*(oldSites : Word w)
  tag : after m (eventLog rs) (nextHead+27) = (role.code : Word w)
  outside : ∀ x, (x < head+15 ∨ head+27 ≤ x) → x ≠ nextHead+14 → x ≠ nextHead+27 →
    after m (eventLog rs) x = m x
  reads : Reads (fun _ => False) (eventLog rs)
  writes : Writes (fun x => (head+15 ≤ x ∧ x<head+27) ∨ x=nextHead+14 ∨ x=nextHead+27) (eventLog rs)
  length : rs.length = 3
  charge : RAMBuckets.cost Report.probes rs = 17
  source : SourceWalk (Source pub st) vis m rs



theorem install (W : Window scr vis) (cap : ℕ) (m : Memory w) (ltBlock : t < blocks)
    (substep : step ≤ S.steps) (fit : endAddress L < 2^w)
    (rows : m (pt).rows.val = (directoryRows L : Word w)) (pitch : m (pub 1-1).val = (levelWords L : Word w))
    (clock : scanCap scr 42 ≤ cap) (oldSites : ℕ) (old : (LevelFields.sites step).eval pub st m = (oldSites : Word w))
    (supported : ∀ mem : Memory w, mem (pt).rows.val = (directoryRows L : Word w) →
      mem (pub 1-1).val = (levelWords L : Word w) → ∀ j ∈ vis, HeaderOperands.Supported D pub st mem j) :
    ∃ ps : List Pkt,
      Group scr L base cap ((scr).initial.length+t*(scr).block.length+W.before.length) (directoryRows L) m ps ∧
      ps.map (fun p => p.stage.phase) = W.indices ∧
      Published B base positions blocks t step role fields m oldSites (ps.flatMap SourceWalk.Packet.reports) := by
  have Hfit : levelStart L 0 < 2^w := (levelStart_mono L (Nat.zero_le _)).trans_lt fit
  have low := Window.lowCells (A := scr) L base rfl rfl Hfit
  have hOld := levelStart_mono L (show 0 ≤ first+step from Nat.zero_le _)
  have hNext := levelStart_mono L (show 0 ≤ first+(step+1) from Nat.zero_le _)
  have hLevel : first+(step+1) < (L).levels := by
    have h := Nat.mul_le_mul_left (S.steps+1) ltBlock
    change (S.steps+1)*t+(step+1)<1+(S.steps+1)*blocks
    rw [Nat.mul_succ] at h
    omega
  let entry : LevelFields.Entry L (first) pub st m := ⟨rfl,pitch⟩
  obtain ⟨rs,walk,cells,successor,tag,other,reads,writes,len,cost⟩ :=
    publish_metadata m entry B.recordLimit (slotDegree S) role fields oldSites old (by change 30 ≤ 54; decide)
      hLevel fit (low.2.trans_le hOld)
  have wr : Writes (levelStart L 0 ≤ ·) (eventLog rs) := by
    intro a v hv
    rcases writes a v hv with h | h | h <;> omega
  have raw : SourceWalk (Window.Raw (A := scr) L base t 42) vis m rs := by
    apply data_walk walk (levelStart L 0) m (fun _ _ => rfl) (fun a v hv => (reads a v hv).elim) wr
    intro j hj mem logs source ag rd wt
    obtain ⟨fuel,r,rfl,positive,bounded,ret,call⟩ := source
    obtain ⟨start,stop⟩ := limits (L).shape step B.recordLimit (slotDegree S) role fields pub st mem j hj
    have one : 1 < 2^w := by
      change (L).base+_+_+_+_+_ < 2^w at Hfit
      omega
    refine ⟨fuel,[[]],bounded,HeaderPacket.singleton positive call ?_ ?_ ?_ ?_,?_⟩
    · rw [start,stop]; apply Fin.lt_def.mpr; change 0 < 1 % (2^w); rw [Nat.mod_eq_of_lt one]; decide
    · exact ret.trans (congrArg some stop.symm)
    · simpa only [eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil] using rd
    · simpa only [eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil] using wt
    · exact supported mem ((ag _ low.1).trans rows) ((ag _ low.2).trans pitch) j hj
  have bounds (j : Fin (scr).size) := SourceOnline.scanCap_clocks
    (p := ⟨HeaderPacket.attach scr j pub st m 42 [[]],m,[]⟩) 42 (by rfl) clock
  have live (j : Fin (vis).length) : Window.ordinal (A := scr) t (W.index j) < directoryRows L := by
    rw [W.ordinal_index,BlockProgram.directory_rows,(scr).calendar_total]
    have pos := (W.position j).isLt
    have mul := Nat.mul_le_mul_right (scr).block.length ltBlock
    rw [Nat.succ_mul] at mul
    omega
  obtain ⟨ps,group,ph,hr⟩ := W.group L base t rfl rfl Hfit cap 42 m rs raw rows pitch
    live (fun j _ => (bounds j).1)
    (fun j _ => (bounds j).2)
  refine ⟨ps,group,ph,?_⟩
  rw [hr]
  exact ⟨cells,successor,tag,other,reads,writes,len,cost,walk⟩

/-- The controller may compose arbitrarily many substeps: metadata writes
touch only two consecutive headers. Earlier levels, later levels and the
live group's control words agree with the source. -/
theorem Published.levelsFrame {m : Memory w} {oldSites : ℕ} {rs : List (Report w)}
    (P : Published B base positions blocks t step role fields m oldSites rs) (x : ℕ)
    (out : x < head ∨ levelStart L (first+step+2) ≤ x) : after m (eventLog rs) x = m x := by
  have advance (j : ℕ) : levelStart L (j+1) = levelStart L j + levelWords L := by
    simp only [levelStart,Nat.succ_mul,Nat.add_assoc]
  have next : nextHead = head+levelWords L := by rw [← Nat.add_assoc,advance]
  have later : levelStart L (first+step+2) = nextHead+levelWords L := by
    rw [show first+step+2=(first+(step+1))+1 by omega,advance]
  have width : 30 ≤ levelWords L := by
    have hh : levelHeaderWords L=66 := rfl
    simp only [levelWords,hh]
    omega
  rw [later,next] at out
  apply P.outside <;> omega

end CompressorRecords.BlockMetadata

end VPVNP
end Computability
end OAI
