import OAI.Computability.VPVNP.PairNodeChildPublishedDirectory
import OAI.Computability.VPVNP.CompressorShrinkScheduledTail
import OAI.Computability.VPVNP.CompressorSelectedPayloadHistory

/-!
# The seven child-scan operands at a selected level

The child decoder reads its old-level directory in one contiguous block
at scalar 14. The following six scalar words come from the pass metadata
packet. Its first word is the carried DFS base, supplied at traversal by
the chronological directory history.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SelectedChildDirectory

open BurstRAM Compression DescriptorSpace PairSimulation.NodeArguments PairSimulation.NodeArguments.ChildScan
open BlockPlanner Schedule
open scoped Fin.CommRing

variable {w a g : ℕ} {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable (L : Layout) (i n : ℕ) (X : State a g) (m : Memory w)

local notation "head" => levelStart L i
local notation "T" => packedIncidence L w i (X.positions*2^a)
local notation "arena" => Arena.mk n (frameStride (slotDegree S) n)

/-- All seven words at the actual header pointer. The first word may be
given as any natural representative of the stored DFS row base. -/
structure Stored : Prop where
  room : head+20 < 2^w
  wide : 20 < levelWords L
  bank : ∀ older : ℕ, m (head+14) = (older : Word w) →
    (directory a older B.recordLimit arena T).Stored m ((head : Word w)+14)

variable {B L i n X m} {out : Memory w}

open private field_address from OAI.Computability.VPVNP.PairNodeChildPublishedDirectory

theorem Stored.stride (d : Stored B L i n X m) : m (head+15) = ((B.recordLimit+2 : ℕ) : Word w) := by
  have h := d.bank (m (head+14)).val (Fin.cast_val_eq_self _).symm 1
  rw [field_address head d.room 1] at h
  exact h

/-- Term, map, and later live scheduler writes preserve the child operands
when they preserve these seven actual cells. -/
theorem Stored.keep (d : Stored B L i n X m)
    (same : ∀ x, head+14 ≤ x → x ≤ head+20 → out x = m x) : Stored B L i n X out :=
  ⟨d.room,d.wide,fun older base => directory_retain
    (d.bank older ((same _ le_rfl (by omega)).symm.trans base)) d.room same⟩

theorem Stored.transfer (d : Stored B L i n X m)
    (same : SourceTransport.Agree (SelectedPayloadHistory.Cells L i) m out) : Stored B L i n X out := by
  apply d.keep
  intro x lo hi
  have edge : levelStart L (i+1) = head+levelWords L := by
    simp only [levelStart,Nat.succ_mul,Nat.add_assoc]
  exact (same x (Or.inl ⟨by omega,by have := d.wide; omega⟩)).symm

variable {workspace : Word w} {positions blocks t : ℕ}
local notation "prog" => BlockProgram.script B
local notation "layout" => BlockProgram.layout B workspace.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog prog)) workspace
local notation "pub" => Ports.data pt
local notation "first" => Script.levelsPerBlock prog*t
local notation "st" => (levelStart layout first : Word w)

private theorem layout_width : 20 < levelWords layout := by
  change 20 < 66+_+_
  omega

open private BlockMetadata.Published.keeps_row_base from OAI.Computability.VPVNP.PairNodeChildPublishedDirectory

section Shrink

variable {j : Fin S.steps} {r : ℕ} {Y : State (ShrinkBlockInputs.a j) (packingLaneBits (ShrinkBlockInputs.a j) r)}
local notation "cur" => first+j.val
local notation "old" => packedIncidence layout w cur (Y.positions*2^(ShrinkBlockInputs.a j))

/-- The actual shrinking metadata writer publishes the old child directory. -/
theorem Stored.of_shrink {start : ℕ} {rs : List (Report w)}
    (p : BlockMetadata.Published B workspace positions blocks t j.val .shrink (BlockMetadata.shrinkFields B j)
      m (ShrinkPreimages.oldCount Y) rs)
    (header : ShrinkHeaderReads.Header j Y old start layout first m)
    (entry : LevelFields.Entry layout first pub st m) (termFits : ShrinkInput.termEnd Y start 10 < 2^w)
    (rows : m (pt).rows.val = (directoryRows layout : Word w))
    (nCell : m (levelStart layout 0+29) = (n : Word w)) :
    Stored B layout cur n Y (after m (eventLog rs)) := by
  refine ⟨by have := header.room; omega,layout_width,fun older rowBase => ?_⟩
  apply p.shrink_child_directory B j Y old start workspace positions blocks t header entry termFits rows n older nCell
  exact (BlockMetadata.Published.keeps_row_base B workspace positions blocks t p).symm.trans rowBase

/-- The shrinking term and data publishers follow the metadata writer in
the same pass and preserve all seven child-scan operands. -/
theorem Stored.of_shrink_tail {cap start : ℕ} {ms ps : List (SourceOnline.Packet prog w)}
    (tail : ShrinkScheduledTail.Result B workspace positions blocks t cap j Y m ms ps)
    (header : ShrinkHeaderReads.Header j Y (packedIncidence layout w cur (DemandRAM.oldCount Y)) start layout first m)
    (pitch : m (pub 1-1).val = (levelWords layout : Word w)) (termFits : ShrinkInput.termEnd Y start 10 < 2^w)
    (rows : m (pt).rows.val = (directoryRows layout : Word w))
    (nCell : m (levelStart layout 0+29) = (n : Word w)) :
    Stored B layout cur n Y (SourceOnline.post m ps) := by
  have count : DemandRAM.oldCount Y = Y.positions*2^(ShrinkBlockInputs.a j) := by
    rw [State.positions,Fintype.card_prod,Fintype.card_congr (bitWordFinEquiv _),Fintype.card_fin]
  have metadata := Stored.of_shrink tail.baseFields (count ▸ header) ⟨rfl,pitch⟩ termFits rows nCell
  exact metadata.keep (fun x _ hi => tail.metaCell x (Or.inl (by omega)))

end Shrink

section Refresh

variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
variable {r : ℕ} (Y : State S.portExponent (S.portExponent+r))
variable (c : Refresh.DyadicRefreshChoice Y S.graph (Nat.two_pow_pos _)
  (S.port_bound.connected_and_pos S.port_order).1 B.refresh) (bits : List Bool)
local notation "lev" => RefreshPlacement.selectedLevel B f hf Y c bits
local notation "cur" => first+S.steps

/-- The selected refresh metadata writer publishes the same child operand
bank for its singleton placement. -/
theorem Stored.of_refresh {rs : List (Report w)} {dH : ℕ}
    (p : BlockMetadata.Published B workspace positions blocks t S.steps .refresh (BlockMetadata.refreshFields B)
      m Y.positions rs)
    (entry : LevelFields.Entry layout first pub st m)
    (header : LevelFields.Published layout cur lev dH m)
    (pointers : PortRefresh.TraversalHeaders.HeadBank layout cur (lev).oldSlots m)
    (room : levelStart layout cur+66 ≤ 2^w) (rows : m (pt).rows.val = (directoryRows layout : Word w))
    (nCell : m (levelStart layout 0+29) = (n : Word w)) :
    Stored B layout cur n Y (after m (eventLog rs)) := by
  refine ⟨by omega,layout_width,fun older rowBase => ?_⟩
  apply p.refresh_child_directory B workspace positions blocks t f hf Y c bits entry header pointers room rows n older nCell
  exact (BlockMetadata.Published.keeps_row_base B workspace positions blocks t p).symm.trans rowBase

end Refresh
end CompressorRecords.SelectedChildDirectory

end VPVNP
end Computability
end OAI
