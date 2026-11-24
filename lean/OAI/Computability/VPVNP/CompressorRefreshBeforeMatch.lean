import OAI.Computability.VPVNP.CompressorRefreshBeforeGroup
import OAI.Computability.VPVNP.CompressorRecordRefreshDeterminism

/-!
# Aligning the deterministic prefix with every selected refresh

The pre - selection reports depend only on the current graph. Thus the
canonical prefix reaches the identical data memory used by every
selected branch, at the selector's actual ordinal in the repeated block.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
set_option quotPrecheck false

namespace CompressorRecords.RefreshBefore

open BurstRAM BlockPlanner Schedule DescriptorSpace Compression
open BlockHeaderRun SourceOnline SourceTransport PairSimulation.LocalHistory
open PortRefresh PortRefresh.LevelRecipe PortRefresh.NewSlots
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
variable {B : S.Templates} {f : B.Entry → R} {hf : B.IsSolution f}
variable {w g : ℕ} {base : Word w} {positions blocks t : ℕ} {X : State S.portExponent
    (S.portExponent + g)}
local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "fl" => Script.levelsPerBlock scr * t
local notation "cur" => fl + S.steps
local notation "nxt" => fl + (S.steps + 1)
local notation "start" => arrayBase L cur
local notation "T" => packedIncidence L w cur (X.positions * 2 ^ S.portExponent)
local notation "s₀" => RefreshBlockPlan.shape B
local notation "P" => PortRefresh.Allocation.plan X (S.degreeExponent 0) (s₀).dH (s₀).ties
  (s₀).stride start
local notation "ties" => RefreshBlockPlan.order B
local notation "origin" => PassOrigin.refresh (B := B) (f := f) (hf := hf) X
local notation "v" => RefreshPlacement.selectedLevel B f hf X (defaultSelection origin) []
local notation "hwin" => RefreshHeaders.window B
local notation "pwin" => RefreshPrepare.window B
local notation "offset" => (scr).initial.length + t * (scr).block.length + (hwin).before.length
local notation "log" => (fun xs : List (Packet scr w) ↦ xs.flatMap SourceWalk.Packet.reports)

variable {cap : ℕ} {m : Memory w} {hs ds : List (Packet (BlockProgram.script B) w)}
variable (b : Before B f hf base positions blocks t X cap m hs ds)

theorem Before.start_offset :
    (hwin).before.length = ((List.finRange S.steps).flatMap (BlockProgram.shrink B)).length := by
  change (BlockGroups.refresh B 0).before.length = _
  rw [BlockGroups.refresh_offset]
  simp

include b in
theorem Before.length : (hs ++ ds).length = 6 + (s₀).ties := by
  have hh : (hwin).indices.length = 3 := by
    rw [Window.indices,List.length_ofFn]
    exact BlockHeaderPlan.substep_length ..
  have dd : (pwin).indices.length = 3 + (s₀).ties := by
    rw [Window.indices,List.length_ofFn,List.length_map]
    simp only [RefreshPrepare.stages,List.length_map,List.length_append,List.length_cons,
      List.length_nil,List.length_finRange]
  calc
    (hs ++ ds).length = ((hwin).indices ++ (pwin).indices).length :=
      (List.length_map _).symm.trans (congrArg List.length b.phases)
    _ = 3 + (3 + (s₀).ties) := (List.length_append ..).trans (congrArg₂ Nat.add hh dd)
    _ = 6 + (s₀).ties := by omega

include b in
theorem Before.selector_offset :
    offset + (hs ++ ds).length =
      (scr).initial.length + t * (scr).block.length + (BlockIndex.blockRefresh B).index.val := by
  rw [b.length,Before.start_offset,BlockIndex.block_refresh_offset]
  omega

include b in
theorem Before.headers_eq (c : Compression.Refresh.DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
    (S.port_bound.connected_and_pos S.port_order).1 B.refresh) (sel : List Bool) :
    post m hs = finalMemory (RefreshPlacement.selectedLevel B f hf X c sel) L cur nxt m := by
  calc
    post m hs = after m (eventLog (reports v L cur nxt m)) :=
      congrArg (fun rs : List (Report w) ↦ after m (eventLog rs)) b.headerReports
    _ = finalMemory v L cur nxt m := reports_after ..
    _ = _ := rfl

include b in
theorem Before.matches (c : Compression.Refresh.DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
    (S.port_bound.connected_and_pos S.port_order).1 B.refresh) (sel : List Bool) {rs : List
      (Report w)}
    {out : Memory w} {fit : (P).segments ≤ 2 ^ w}
    (other : PrepareRun X T ((P).scratch w) (word (P).demand) ties (word (2 ^ g)) fit
      (finalMemory (RefreshPlacement.selectedLevel B f hf X c sel) L cur nxt m) out rs) :
    log ds = rs ∧ post m (hs ++ ds) = out := by
  rw [← b.headers_eq c sel] at other
  rw [post_append]
  exact PrepareRun.deterministic b.data.run other

include b in
/-- The header fields depend on the input dimensions, which are shared by all terms. -/
theorem Before.counts_for
    (c : Compression.Refresh.DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
      (S.port_bound.connected_and_pos S.port_order).1 B.refresh) (sel : List Bool) :
    let u := RefreshPlacement.selectedLevel B f hf X c sel
    LevelFields.Published L cur u (Scalars.ofOrigin u.origin).expanderDegree (post m hs) :=
  ⟨b.counts.room,b.counts.vertices,b.counts.degree,b.counts.lanes,b.counts.residual,
    b.counts.nextDegree,b.counts.expander⟩

/-- The same three native publishers certify every selected successor's header. -/
theorem Before.header_for
    (c : Compression.Refresh.DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
      (S.port_bound.connected_and_pos S.port_order).1 B.refresh) (sel : List Bool) :
    let u := RefreshPlacement.selectedLevel B f hf X c sel
    Substep u L ⟨cur,b.oldLive⟩ ⟨nxt,b.newLive⟩ (by change 6 ≤ 54; decide) m := by
  intro u
  have published := b.counts_for c sel
  rw [b.headers_eq c sel] at published
  exact ⟨b.headerRun.relabel,b.headerRun.advance,b.headerRun.heads,published,
    b.headerRun.output,b.headerRun.firstCounts,b.headerRun.outside⟩

end CompressorRecords.RefreshBefore

end

end VPVNP
end Computability
end OAI
