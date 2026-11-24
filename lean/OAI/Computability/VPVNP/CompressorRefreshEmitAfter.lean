import OAI.Computability.VPVNP.CompressorRefreshPlacementEmission
import OAI.Computability.VPVNP.CompressorRefreshCoreBuild
import OAI.Computability.VPVNP.CompressorRefreshCopyGroup
import OAI.Computability.VPVNP.CompressorRefreshPayloadSpace
import OAI.Computability.VPVNP.CompressorDeterministicGroup

/-! # The canonical incidence and traversal output following a selected refresh -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.RefreshEmit

open BurstRAM BlockPlanner Compression DescriptorSpace PortRefresh PhaseRecipe Schedule
open SourceOnline SourceTransport
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
variable {g w : ℕ} (base : Word w) (positions blocks t cap : ℕ)
variable (f : B.Entry → R) (hf : B.IsSolution f) (X : State S.portExponent (S.portExponent + g))
local notation "he" => Nat.two_pow_pos S.expanderExponent
local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "hd" => And.right S.degree_bounds
variable (c : Refresh.DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
  (S.port_bound.connected_and_pos S.port_order).1 B.refresh) (sel : List Bool)

local notation "level" => RefreshPlacement.selectedLevel B f hf X c sel
local notation "Y" => Refresh.dyadicRefreshNext X S.graph he hc B.refresh S.port_order hd c
local notation "N" => State.positions Y * 2 ^ (S.degreeExponent 0)
local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "first" => Script.levelsPerBlock scr * t
local notation "cur" => (first) + S.steps
local notation "nxt" => (first) + (S.steps + 1)
local notation "head" => levelStart L (cur)
local notation "start" => arrayBase L (cur)
local notation "orig" => packedIncidence L w (cur) (SelectedLevel.oldSlots level)
local notation "shape" => RefreshBlockPlan.shape B
local notation "P" => Allocation.plan X (S.degreeExponent 0) (LevelRecipe.Shape.dH shape)
  (LevelRecipe.Shape.ties shape) (LevelRecipe.Shape.stride shape) start
local notation "W₂" => BlockGroups.refresh B 2
local notation "W₃" => BlockGroups.refresh B 3
local notation "W₄" => BlockGroups.refresh B 4
local notation "W₅" => BlockGroups.refresh B 5
local notation "W₆" => BlockGroups.refresh B 6
local notation "off" => List.length (Script.initial scr) + t * List.length (Script.block scr)

/-- Reports and data readbacks for the six incidence copies and the nine
placement and traversal publications, in their actual order. -/
structure After (m : Memory w) (copies publications : List (Packet scr w)) : Prop where
  group : SourceOnline.Group scr L base cap (off + (W₂).before.length) (directoryRows L) m
    (copies ++ publications)
  phases : (copies ++ publications).map (fun p => p.stage.phase) =
    (W₂).indices ++ (((W₃).indices ++ (W₄).indices) ++ ((W₅).indices ++ (W₆).indices))
  count : (copies ++ publications).length = 15
  quiet : ∀ p ∈ copies ++ publications, p.stage.choices = List.replicate p.stage.choices.length []
  charge : RAMBuckets.cost Report.probes ((copies ++ publications).flatMap SourceWalk.Packet.reports) ≤
    X.positions * (18 * 2 ^ (S.degreeExponent 0) + 4) + 27
  copied : RefreshCopyPackets.Copied B base positions blocks t X c m (copies.flatMap SourceWalk.Packet.reports)
  installed : RefreshPlacement.TailResult B base positions blocks t cap f hf X c sel
    (post m copies) publications

/-- The six canonical copies charge three units per populated cell. The remaining
nine visits contribute the placement scan and the fixed header publications. -/
theorem After.charge_eq {m : Memory w} {copies publications : List (Packet scr w)}
    (out : After B base positions blocks t cap f hf X c sel m copies publications) :
    RAMBuckets.cost Report.probes ((copies ++ publications).flatMap SourceWalk.Packet.reports) =
      9 * (Fintype.card (Y).Base * 2^(S.degreeExponent 0)) +
      9 * (X.positions * 2^(S.degreeExponent 0)) + 4 * X.positions + 27 := by
  rw [List.flatMap_append,RAMBuckets.cost_append,out.copied.charge,out.copied.calls,out.installed.charge,
    Refresh.dyadicRefreshNext_positions X S.graph he hc B.refresh S.port_order hd c]
  omega

private theorem published_keep {layout : Layout} {idx dH : ℕ} {v : SelectedLevel B f hf}
    {m m' : Memory w} (old : LevelFields.Published layout idx v dH m)
    (kept : ∀ n < 6, m' (levelStart layout idx + n) = m (levelStart layout idx + n)) :
    LevelFields.Published layout idx v dH m' :=
  ⟨old.room, (kept 0 (by decide)).trans old.vertices, (kept 1 (by decide)).trans old.degree,
    (kept 2 (by decide)).trans old.lanes, (kept 3 (by decide)).trans old.residual,
    (kept 4 (by decide)).trans old.nextDegree, (kept 5 (by decide)).trans old.expander⟩

private theorem copy_paths {a b : ℕ} (Z : State a b) (T U : IncidenceDirectory w) (m : Memory w) :
    let rs := CopyIncidence.reports Z T U CopyIncidence.allColumns m
    branchPaths rs = List.replicate rs.length [] := by
  intro rs
  have h := (CopyIncidence.reports_work Z T U CopyIncidence.allColumns m).2.2
  exact List.map_eq_replicate_iff.mpr (fun r hr => (h r hr).2.2)

open private offset_length from OAI.Computability.VPVNP.CompressorBlockHeadSequence

set_option maxHeartbeats 900000 in
private theorem after_of_groups (mid : Memory w) (qs ps : List (Packet scr w))
    (grp : SourceOnline.Group scr L base cap (off + (W₂).before.length) (directoryRows L) mid qs)
    (lab : qs.map (fun p => p.stage.phase) = (W₂).indices)
    (copied : RefreshCopyPackets.Copied B base positions blocks t X c mid (qs.flatMap SourceWalk.Packet.reports))
    (done : RefreshPlacement.TailResult B base positions blocks t cap f hf X c sel (post mid qs) ps) :
    After B base positions blocks t cap f hf X c sel mid qs ps := by
  have len : qs.length = 6 := by
    have h := congrArg List.length lab
    simp only [List.length_map, Window.indices, List.length_ofFn] at h
    exact h
  have nps : ps.length = 9 := by
    have h := congrArg List.length done.phases
    simp only [List.length_map, List.length_append, Window.indices, List.length_ofFn] at h
    exact h.trans (by rfl)
  have offNext : off + (W₂).before.length + qs.length = off + (W₃).before.length := by
    have step := offset_length (BlockGroups.refreshParts B) 2
      (by rw [BlockGroups.refreshParts_length]; decide)
    have six : ((BlockGroups.refreshParts B)[2]'(by rw [BlockGroups.refreshParts_length]; decide)).length = 6 :=
      List.length_ofFn ..
    rw [six] at step
    rw [len, BlockGroups.refresh_offset, BlockGroups.refresh_offset]
    change off + (_ + ((BlockGroups.refreshParts B).take 2).flatten.length) + 6 =
      off + (_ + ((BlockGroups.refreshParts B).take 3).flatten.length)
    rw [step]; omega
  have qbits := PublishedHeads.chronological_tapes mid qs grp.chronological
  rw [copied.reports_eq, copy_paths] at qbits
  have allSites := Refresh.dyadicRefreshNext_positions X S.graph he hc B.refresh S.port_order hd c
  have vertices : Fintype.card (Y).Base ≤ (Y).positions := by
    unfold State.positions
    rw [Fintype.card_prod]; exact Nat.le_mul_of_pos_right _ Fintype.card_pos
  have calls := copied.calls
  have le := Nat.mul_le_mul_right (2 ^ S.degreeExponent 0) vertices
  rw [allSites] at calls le
  have nextGroup : SourceOnline.Group scr L base cap (off + (W₂).before.length + qs.length)
      (directoryRows L) (post mid qs) ps :=
    Eq.mp (congrArg (fun i => SourceOnline.Group scr L base cap i (directoryRows L) (post mid qs) ps) offNext.symm) done.group
  refine ⟨grp.append nextGroup, ?_, ?_, ?_, ?_, copied, done⟩
  · rw [List.map_append, lab, done.phases]
  · rw [List.length_append, len, nps]
  · intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact ScheduledTrace.packet_quiet_of_flat qbits p h
    · exact ScheduledTrace.packet_quiet_of_flat done.tapes p h
  · rw [List.flatMap_append, RAMBuckets.cost_append, copied.charge, done.charge, Nat.mul_add]
    have h := Nat.mul_le_mul_left 3 le
    linarith only [calls, h]


set_option maxHeartbeats 950000 in
/-- Complete every post-core window from the actual core's stored temporary graph. -/
theorem after_core (termCap : ℕ) (m : Memory w) (rs : List (Report w)) (live : t < blocks)
    (size : X.positions ≤ positions) (fit : endAddress L < 2 ^ w)
    (clock : scanCap scr 42 ≤ cap) (rows : m (pt).rows.val = (directoryRows L : Word w))
    (pitch : m ((pt).directory - 1).val = (levelWords L : Word w))
    (dH : ℕ) (old : LevelFields.Published L (cur) level dH m)
    (oldHeads : TraversalHeaders.HeadBank L (cur) (level).oldSlots m)
    (newHeads : TraversalHeaders.HeadBank L (nxt) N m)
    (built : RefreshCore.Built B base positions blocks t X c termCap m rs) :
    ∃ copies publications,
      After B base positions blocks t cap f hf X c sel (after m (eventLog rs)) copies publications := by
  let mid := after m (eventLog rs)
  have space := RefreshPayloadHistory.Space.ofLayout B base positions blocks t X live size fit
  have next : cur + 1 = nxt := Nat.add_assoc ..
  have headerLo := space.header_before
  have stop := space.scratch_next
  rw [next] at stop
  have lo (x : ℕ) (hx : x < start) : mid x = m x :=
    after_outside m built.writes (fun h => hx.not_ge h.1)
  have hi (x : ℕ) (hx : levelStart L (nxt) ≤ x) : mid x = m x :=
    after_outside m built.writes (fun h => h.2.not_ge (stop.trans hx))
  have bank₁ := newHeads.keep (fun n _ => hi _ (Nat.le_add_right ..))
  have hdrFit := PublishedHeads.level_room B base positions blocks t S.steps live le_rfl fit
  have header := RefreshCore.Header.ofPublished old oldHeads rfl (show 0 < 6 by decide) (by omega)
  have data₁ := header.keep (m' := mid) (fun n hn => lo _ (by omega))
  have ctl := Window.lowCells (A := scr) L base rfl rfl
    ((levelStart_mono L (Nat.zero_le (L).levels)).trans_lt fit)
  have low := space.header_first
  have rows₁ := (lo _ (ctl.1.trans_le (by omega))).trans rows
  have pitch₁ := (lo _ (ctl.2.trans_le (by omega))).trans pitch
  have cap12 : scanCap scr 12 ≤ cap := by unfold scanCap at clock ⊢; omega
  obtain ⟨qs, grp, lab, copied⟩ := RefreshCopyPackets.group B base positions blocks t X c cap
    mid orig live size fit rows₁ pitch₁ cap12 data₁ bank₁ built.represents
  let out := post mid qs
  have tableEarly := space.array_before
  rw [next] at tableEarly
  have keep (x : ℕ) (hx : x < start) : out x = m x := by
    apply (copied.frame x (.inl (hx.trans_le (tableEarly.trans (Nat.le_add_right ..))))).trans
    exact lo x hx
  have hnew := published_keep B f hf old
    (m' := out) (fun n hn => keep _ (by omega))
  have heads₂ := oldHeads.keep (m' := out) (fun n hn => keep _ (by change n < 66 at hn; omega))
  have rows₂ := (keep _ (ctl.1.trans_le (by omega))).trans rows
  have pitch₂ := (keep _ (ctl.2.trans_le (by omega))).trans pitch
  obtain ⟨ps, done⟩ := RefreshPlacement.install_tail B base positions blocks t cap f hf X c sel
    out live size fit rows₂ pitch₂ clock dH hnew heads₂
  exact ⟨qs, ps, after_of_groups B base positions blocks t cap f hf X c sel mid qs ps grp lab copied done⟩

end CompressorRecords.RefreshEmit

end

end VPVNP
end Computability
end OAI
