import OAI.Computability.VPVNP.PairRefreshSelectedOccurrence
import OAI.Computability.VPVNP.PairRefreshSelectedSite

/-! # Native refresh parser on the complete selected branch

The popped address determines both the chronological term and its output site.
Its local reader uses the input state and the term stored in that occurrence,
together with the physical arenas of the block. All rows use the same native
refresh entry and return address.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.SelectedRows

set_option maxHeartbeats 1500000
open scoped Fin.CommRing

open BurstRAM BurstRAM.PrivateRAM Compression CompressorRecords DescriptorSpace
open TraversalRows TraversalRoles ShrinkRoleDirectory DFS LiveProgram VertexImage

variable {k : Type} {K : Type*} [_root_.Field k] [CommRing K] {S : BlockSchedule k} {B : S.Templates}
  {f : B.Entry → K} {hf : B.IsSolution f}
  (n hist w start positions blocks width : ℕ) (leaf : TaggedLayer) (passes : List (SelectedLevel B f hf))

local notation "tags₀" => leaf :: outputTags passes
local notation "base₀" => endAddress (BlockProgram.layout B start positions blocks)

/-- Space required by the real selected state, term and port on each refresh
row. The prefix supplies this bound before the terminal visit starts. -/
def Rooms : Prop := ∀ x : Row passes, RowRoom B n hist w start positions blocks x.occurrence.state
  x.occurrence.choice x.occurrence.port x.val.1.val (tags₀)

variable (room : Rooms n hist w start positions blocks leaf passes)

/-- Freeze the physical row addresses, incidence directories and geometry
using the selected origin of this site. -/
noncomputable def rowSite (x : Row passes) : RefreshHook.Site B n hist w :=
  ofSelected B n hist w start positions blocks x.occurrence.state x.occurrence.choice
    x.occurrence.port x.val.1.val (tags₀) width (room x)

local notation "site₀" => rowSite n hist w start positions blocks width leaf passes room
local notation "ties₀" => RefreshBlockPlan.order B
local notation "stride₀" => PortRefresh.LevelRecipe.Shape.stride (RefreshBlockPlan.shape B)

theorem parent_eq (x : Row passes) : ((site₀) x).parent =
    ShrinkRoleDirectory.address B.recordLimit (base₀) leaf passes x.val := by
  change TraversalRows.address B.recordLimit (layerBase B.recordLimit (base₀) (tags₀) (x.val.1.val + 1))
    (PortRefresh.NewSlots.sites x.occurrence.state.baseIndex (bitWordFinEquiv _) x.occurrence.port).val = _
  rw [x.occurrence.ordinal]
  rfl

variable (order : B.Entry ≃ Fin hist) (pub : Fin 11 → Word w) (m : Memory w)

/-- The global hook accepts only a decoded refresh parent and runs exactly
the reader of that physical row. -/
noncomputable def parser : HookParser w n where
  read node s bits := (decode (base₀) leaf passes node).bind fun x =>
    (((site₀) x).hook (ties₀) (stride₀) order pub m).read node s bits

local notation "reader₀" => SelectedRows.parser n hist w start positions blocks width leaf passes room order

/-- The exact union of prepared refresh rows of this branch. -/
def Prepared (node : Word w) (s : Scratch w n) : Prop := ∃ x : Row passes, ((site₀) x).Prepared node s

local notation "ready₀" => Prepared n hist w start positions blocks width leaf passes room

variable (fit : layerBase B.recordLimit (endAddress (BlockProgram.layout B start positions blocks))
    (leaf :: outputTags passes) (passes.length + 1) ≤ 2 ^ w)

include fit in
theorem read_at (x : Row passes) (node : Word w) (s : Scratch w n) (atRow : ((site₀) x).Prepared node s)
    (bits : List Bool) :
    ((reader₀) pub m).read node s bits = (((site₀) x).hook (ties₀) (stride₀) order pub m).read node s bits := by
  have ptr : node.val = ((site₀) x).parent := atRow.1
  have addr : node.val = ShrinkRoleDirectory.address B.recordLimit (base₀) leaf passes x.val :=
    ptr.trans (parent_eq n hist w start positions blocks width leaf passes room x)
  have located : SelectedRows.decode (base₀) leaf passes node = some x :=
    (SelectedRows.decode_eq_some_iff (B := B) (f := f) (hf := hf) (w := w) (base₀) leaf passes fit node x).2 addr
  exact congrArg (fun y : Option (Row passes) => y.bind fun i =>
    (((site₀) i).hook (ties₀) (stride₀) order pub m).read node s bits) located

/-- Prepared scratch at a popped parent identifies a unique selected refresh
site even when two levels chose identical terms. -/
theorem prepared_unique (node : Word w) (s : Scratch w n) (prepared : (ready₀) node s) :
    ∃! x : Row passes, ((site₀) x).Prepared node s := by
  obtain ⟨x, hx⟩ := prepared
  refine ⟨x, hx, fun y hy => unique_row (base₀) leaf passes ?_⟩
  rw [← parent_eq n hist w start positions blocks width leaf passes room y,
    ← parent_eq n hist w start positions blocks width leaf passes room x, ← hy.1, ← hx.1]

/-- The physical dispatch probe on this domain reads the refresh tag. -/
theorem dispatch_prepared {offset : ℕ}
    (tags : TraversalRoles.Reads w m offset B.recordLimit (base₀) (tags₀))
    (codes : 2 < 2 ^ w) (tagFit : offset + (base₀) + tagWords B.recordLimit (tags₀) ≤ 2 ^ w)
    (node : Word w) (s : Scratch w n) (prepared : (ready₀) node s) :
    NodeDispatch.role (m ((offset : Word w) + node).val) = .refresh := by
  obtain ⟨x, hx⟩ := prepared
  have addressEq := hx.1.trans (parent_eq n hist w start positions blocks width leaf passes room x)
  rw [dispatch_at_site B.recordLimit (base₀) leaf passes tags codes tagFit node x.val addressEq, x.property]
  rfl

end PairSimulation.RefreshHook.SelectedRows

end VPVNP
end Computability
end OAI
