import OAI.Computability.VPVNP.CompressorBlockMetadataShrinkReadback
import OAI.Computability.VPVNP.CompressorRefreshPlacementPacket
import OAI.Computability.VPVNP.PairNodeChildStage
import OAI.Computability.VPVNP.PairTraversalControllerInputs

/-!
# The child decoder's directory in the published DFS level

The retained row base occupies scalar 14. The metadata writer publishes the
row stride, old degree, argument arena and stride, inverse-incidence pointer
and width pointer in scalars 15 through 20. These seven consecutive words
are the operand bank read by the native child header.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NodeArguments.ChildScan

open BurstRAM CompressorRecords BlockMetadata
open scoped Fin.CommRing

variable {w : ℕ}

private theorem field_address (head : ℕ) (fit : head + 20 < 2 ^ w) (j : Fin 7) :
    (((head : Word w) + 14) + (j.val : Word w)).val = head + 14 + j.val := by
  have hj := j.isLt
  rw [show (14 : Word w) = ((14 : ℕ) : Word w) from rfl, ← Nat.cast_add, ← Nat.cast_add,
    Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]

/-- The first six metadata operands after the retained row pointer are the
six remaining words consumed by the child decoder. -/
theorem directory_of_payload (m : Memory w) (a older cap slots n oldSites head : ℕ)
    (T : IncidenceDirectory w) (placement : Placement) (fit : head + 20 < 2 ^ w)
    (start : m (head + 14) = (older : Word w))
    (published : ∀ j : Fin 12, m (head + 15 + j.val) =
      (payload cap slots (2 ^ a) n T.actualIn.val T.width.val oldSites placement j : Word w)) :
    (directory a older cap ⟨n, frameStride slots n⟩ T).Stored m ((head : Word w) + 14) := by
  intro j
  rw [field_address head fit j]
  cases j using Fin.cases with
  | zero => exact start
  | succ j =>
    have h := published (j.castAdd 6)
    change m (head + 15 + j.val) = _ at h
    rw [show head + 14 + j.succ.val = head + 15 + j.val by simp only [Fin.val_succ]; omega, h]
    fin_cases j <;> simp [payload, directory, ChildHeader.Fields.words]

/-- Later planner and traversal reports may change memory anywhere outside
these seven words while preserving the decoder's operand bank. -/
theorem directory_retain {f : ChildHeader.Fields w} {m m' : Memory w} {head : ℕ}
    (old : f.Stored m ((head : Word w) + 14)) (fit : head + 20 < 2 ^ w)
    (frame : ∀ i, head + 14 ≤ i → i ≤ head + 20 → m' i = m i) :
    f.Stored m' ((head : Word w) + 14) := by
  intro j
  have addr := field_address head fit j
  have hj := j.isLt
  exact (frame _ (by rw [addr]; omega) (by rw [addr]; omega)).trans (old j)

open DescriptorSpace TraversalControllerInputs TraversalRoles

/-- The child handoff's old-level pointer names the retained seven fields in
the actual traversal memory. The bootstrap supplies the first header and the
level pitch, and the traversal frame preserves every cell before its rows. -/
theorem directory_at_locator (L : Layout) (level : Fin L.levels) {pub : Fin 11 → Word w}
    {src mem : Memory w} {H offset cap : ℕ} {initial : TaggedLayer} {ls : List (Fiber w)}
    (d : Resident pub mem H (levelStart L 0) (levelWords L) offset cap (endAddress L) initial ls)
    {f : ChildHeader.Fields w} (old : f.Stored src ((levelStart L level : Word w) + 14))
    (wide : 21 ≤ levelHeaderWords L) (fit : endAddress L ≤ 2 ^ w)
    (frame : ∀ i < endAddress L, mem i = src i) :
    f.Stored mem (levelHead pub mem level + 14) := by
  have ptr : levelHead pub mem level = (levelStart L level : Word w) := by
    rw [levelHead, terminal_read d 16 (by decide), terminal_read d 17 (by decide),
      d.firstHead, d.levelPitch]
    simp [levelStart]
  have next := levelStart_mono L level.isLt
  change levelStart L (level.val + 1) ≤ endAddress L at next
  have width : levelHeaderWords L ≤ levelWords L := by unfold levelWords; omega
  have bound : levelStart L level + 20 < endAddress L := by
    have adv : levelStart L (level.val + 1) = levelStart L level + levelWords L := by
      simp only [levelStart, Nat.succ_mul, Nat.add_assoc]
    omega
  rw [ptr]
  exact directory_retain old (bound.trans_le fit) fun i _ hi => frame i (hi.trans_lt bound)

end PairSimulation.NodeArguments.ChildScan

namespace CompressorRecords.BlockMetadata

open BurstRAM Compression DescriptorSpace BlockPlanner Schedule ShrinkBlockInputs
open PairSimulation.NodeArguments PairSimulation.NodeArguments.ChildScan
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
  {w g : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (T : IncidenceDirectory w) (start : ℕ)
  (base : Word w) (positions blocks t : ℕ)

local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "pub" => Ports.data pt
local notation "first" => Script.levelsPerBlock scr * t
local notation "st" => (levelStart L first : Word w)
local notation "head" => levelStart L (first + i.val)

private theorem Published.keeps_row_base {step oldSites : ℕ} {role : Role} {fields : Fields}
    {m : Memory w} {rs : List (Report w)}
    (P : Published B base positions blocks t step role fields m oldSites rs) :
    after m (eventLog rs) (levelStart L (first + step) + 14) =
      m (levelStart L (first + step) + 14) := by
  have next : levelStart L (first + (step + 1)) = levelStart L (first + step) + levelWords L := by
    unfold levelStart
    ring
  have wide : 66 ≤ levelWords L := by
    have h : levelHeaderWords L = 66 := rfl
    simp only [levelWords, h]
    omega
  exact P.outside _ (Or.inl (by omega)) (by rw [next]; omega) (by rw [next]; omega)

/-- The actual three selected metadata publications give the child directory
in their post-memory. Scalar 14 is inherited from the preceding publication. -/
theorem Published.shrink_child_directory {m : Memory w} {rs : List (Report w)}
    (P : Published B base positions blocks t i.val .shrink (shrinkFields B i) m
      (ShrinkPreimages.oldCount X) rs)
    (header : ShrinkHeaderReads.Header i X T start L first m)
    (entry : LevelFields.Entry L first pub st m) (termFits : ShrinkInput.termEnd X start 10 < 2 ^ w)
    (rows : m (pt).rows.val = (directoryRows L : Word w))
    (n older : ℕ) (nCell : m (levelStart L 0 + 29) = (n : Word w))
    (rowBase : m (head + 14) = (older : Word w)) :
    (directory (a i) older B.recordLimit ⟨n, frameStride (slotDegree S) n⟩ T).Stored
      (after m (eventLog rs)) ((head : Word w) + 14) := by
  apply directory_of_payload _ _ _ _ _ _ (ShrinkPreimages.oldCount X) _ _
    (shrinkPlacement i X start) (by have := header.room; omega)
  · exact (P.keeps_row_base B base positions blocks t).trans rowBase
  · exact P.shrink_payload B i X T start base positions blocks t header entry termFits rows n nCell

section Refresh

variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
  (Y : State S.portExponent (S.portExponent + g))
  (c : Compression.Refresh.DyadicRefreshChoice Y S.graph (Nat.two_pow_pos _)
    (S.port_bound.connected_and_pos S.port_order).1 B.refresh) (sel : List Bool)

local notation "lev" => RefreshPlacement.selectedLevel B f hf Y c sel
local notation "cur" => first + S.steps
local notation "here" => levelStart L cur
local notation "U" => packedIncidence L w cur (SelectedLevel.oldSlots lev)

/-- At a refresh the same seven words describe the unique older child. The
degree comes from the selected refresh scalar, and the two incidence bases
come from its packed old-level head bank. -/
theorem Published.refresh_child_directory {m : Memory w} {rs : List (Report w)} {dH : ℕ}
    (P : Published B base positions blocks t S.steps .refresh (refreshFields B) m Y.positions rs)
    (entry : LevelFields.Entry L first pub st m)
    (scalars : LevelFields.Published L cur lev dH m)
    (pointers : PortRefresh.TraversalHeaders.HeadBank L cur (lev).oldSlots m)
    (room : here + 66 ≤ 2 ^ w) (rows : m (pt).rows.val = (directoryRows L : Word w))
    (n older : ℕ) (nCell : m (levelStart L 0 + 29) = (n : Word w))
    (rowBase : m (here + 14) = (older : Word w)) :
    (directory S.portExponent older B.recordLimit ⟨n, frameStride (slotDegree S) n⟩ U).Stored
      (after m (eventLog rs)) ((here : Word w) + 14) := by
  let table := tableBase L cur (4 : Fin 6)
  let place : Placement := ⟨Y.positions, table, table + Y.positions, table + 2 * Y.positions, 1⟩
  obtain ⟨_, count, owner, counts, ids, cap⟩ :=
    RefreshPlacement.metadata_values B base positions blocks t f hf Y c sel m dH
      entry scalars pointers room
  have placed : place.reads (refreshFields B) pub st m := ⟨count, owner, counts, ids, cap⟩
  have firstHead := BlockHeaderPlan.firstHeader_eval L base m st (Fin.cast_val_eq_self _).symm rows
  have early := levelStart_mono L (Nat.zero_le (cur))
  have degree := (LevelFields.eval_scalar entry S.steps 1 (by omega)).trans scalars.degree
  have col (q : Fin 6) : (LevelFields.incidence (L).shape S.steps q).eval pub st m =
      ((U).column q).val := by
    rw [LevelFields.eval_incidence entry, packed_column]
    · exact (pointers.incidence q).trans (Fin.cast_val_eq_self _).symm
    · change here + 54 + q.val < 2 ^ w
      have := q.isLt
      omega
  apply directory_of_payload _ _ _ _ _ _ Y.positions _ _ place (by omega)
  · exact (P.keeps_row_base B base positions blocks t).trans rowBase
  · intro j
    exact (P.payload j).trans (field_values B.recordLimit (slotDegree S) (refreshFields B)
      place firstHead (by omega) nCell degree (LevelFields.eval_dimensions entry scalars).1
      (col 4) (col 5) placed j)

end Refresh

end CompressorRecords.BlockMetadata

end VPVNP
end Computability
end OAI
