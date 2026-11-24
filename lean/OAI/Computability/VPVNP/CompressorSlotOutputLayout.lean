import OAI.Computability.VPVNP.CompressorSlotLevel
import OAI.Computability.VPVNP.CompressorRecordIncidenceLayout

/-!
# The six shared columns of a shrinking output

The sorted slot pass already writes the base mate and displacement. Allocate
the base inverse, actual forward and inverse, and outgoing widths in the
following address ranges. Their lengths are the actual numbers of base or
lifted slots. The full six-column directory then supplies subsequent passes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSlots

open SlotLevel BurstRAM Compression Slots

variable (s : Shape) (h : Heads)

/-- Number of outgoing ports in the next graph across all packed sites and residual lanes. -/
def actualCount := sites s*s.newDegree
/-- First address after the base displacement table, reserved for the inverse base matching. -/
def inverseBaseHead := stopAddress s h
/-- Start of the outgoing actual mate column, immediately after the inverse base matching. -/
def outHead := inverseBaseHead s h+baseArcs s
/-- Start of the incoming actual mate column, immediately after the outgoing actual mates. -/
def inHead := outHead s h+actualCount s
/-- Start of the outgoing actual width column, immediately after the incoming actual mates. -/
def widthHead := inHead s h+actualCount s
/-- First free address following the last outgoing width in the shrinking output directory. -/
def finish := widthHead s h+actualCount s

/-- Source and destination addresses for scattering the forward base matching into its inverse. -/
def inverseBank (w : ℕ) : Fin 2 → Word w := (Fin.ofNat (2^w)) ∘ ![targetsHead s h,inverseBaseHead s h]

/-- Public degree, lane count, matching, displacement, and destination parameters for lifting
the forward or inverse base matching to actual ports. -/
def actualBank (reverse : Bool) (w : ℕ) : Fin 5 → Word w :=
  (Fin.ofNat (2^w)) ∘ ![s.newDegree,s.lanes,if reverse then inverseBaseHead s h else targetsHead s h,
    shiftsHead s h,if reverse then inHead s h else outHead s h]

/-- The radices, genuine range bound, and row, split-width, and output addresses used to gather
widths in actual outgoing-port order. -/
def widthBank (splitHead w : ℕ) : Fin 8 → Word w :=
  (Fin.ofNat (2^w)) ∘ ![s.newDegree,s.lanes,∑t,s.subdivisions t,oldBaseArcCount s.bases s.tags s.oldDegree s.colors,
    keyCount s.bases s.tags s.oldDegree s.colors s.subdivisions*s.lanes,rowsHead s h,splitHead,widthHead s h]

/-- Assemble the six public column addresses for the next state's base mates, displacements,
actual mates, and widths. -/
def directory (w : ℕ) : IncidenceDirectory w :=
  ⟨Fin.ofNat _ (targetsHead s h),Fin.ofNat _ (inverseBaseHead s h),Fin.ofNat _ (shiftsHead s h),
    Fin.ofNat _ (outHead s h),Fin.ofNat _ (inHead s h),Fin.ofNat _ (widthHead s h)⟩

/-- Natural-address readback of the six arrays in their canonical finite port orders. -/
structure Stored {a l w : ℕ} (Y : State a l) (m : Memory w) : Prop where
  baseOut : ∀ e, m (targetsHead s h+(IncidenceDirectory.baseOrder Y e).val) =
    Fin.ofNat _ (IncidenceDirectory.baseOrder Y (Y.slots.base.target e)).val
  baseIn : ∀ e, m (inverseBaseHead s h+(IncidenceDirectory.baseOrder Y e).val) =
    Fin.ofNat _ (IncidenceDirectory.baseOrder Y (Y.slots.base.target.symm e)).val
  shift : ∀ e, m (shiftsHead s h+(IncidenceDirectory.baseOrder Y e).val) =
    Fin.ofNat _ (bitWordFinEquiv l (Y.slots.displacement e)).val
  actualOut : ∀ e, m (outHead s h+(IncidenceDirectory.actualOrder Y e).val) =
    Fin.ofNat _ (IncidenceDirectory.actualOrder Y (Y.slots.actualGraph.target e)).val
  actualIn : ∀ e, m (inHead s h+(IncidenceDirectory.actualOrder Y e).val) =
    Fin.ofNat _ (IncidenceDirectory.actualOrder Y (Y.slots.actualGraph.target.symm e)).val
  width : ∀ e, m (widthHead s h+(IncidenceDirectory.actualOrder Y e).val) = Fin.ofNat _ (Y.width ((e.1.1,e.2),e.1.2))

private theorem add_index {w n : ℕ} (base : ℕ) (i : Fin n) (bound : base+n ≤ 2^w) :
    ((Fin.ofNat (2^w) base : Word w)+Fin.ofNat _ i.val).val=base+i.val := by
  have hi := i.isLt
  rw [Fin.val_add,Fin.val_ofNat,Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : base < 2^w),
    Nat.mod_eq_of_lt (by omega : i.val < 2^w),Nat.mod_eq_of_lt (by omega)]

/-- The numeric arrays are precisely the common incidence directory expected
by the next cursor, shrink or refresh calculation. -/
theorem Stored.represents {s : Shape} {h : Heads} {a l w : ℕ} {Y : State a l} {m : Memory w}
    (data : Stored s h Y m) (hb : Fintype.card Y.Base*2^a=baseArcs s)
    (ha : Fintype.card Y.Base*2^l*2^a=actualCount s) (fit : finish s h < 2^w) :
    (directory s h w).Represents Y m := by
  have h₁ : targetsHead s h+baseArcs s=shiftsHead s h := rfl
  have h₂ : shiftsHead s h+baseArcs s=inverseBaseHead s h := rfl
  have h₃ : inverseBaseHead s h+baseArcs s=outHead s h := rfl
  have h₄ : outHead s h+actualCount s=inHead s h := rfl
  have h₅ : inHead s h+actualCount s=widthHead s h := rfl
  have h₆ : widthHead s h+actualCount s=finish s h := rfl
  constructor <;> intro e <;> simp only [IncidenceDirectory.basePort_number,IncidenceDirectory.actualPort_number,
    directory,CursorRAM.encode] <;> rw [add_index _ _ (by omega)]
  · exact data.baseOut e
  · exact data.baseIn e
  · exact data.shift e
  · exact data.actualOut e
  · exact data.actualIn e
  · exact data.width e

end CompressorRecords.ShrinkSlots

end VPVNP
end Computability
end OAI
