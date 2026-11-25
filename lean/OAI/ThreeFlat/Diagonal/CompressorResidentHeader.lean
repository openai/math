import OAI.ThreeFlat.Diagonal.CompressorPhysicalWidthRow
import OAI.ThreeFlat.Diagonal.CompressorStageDimensions

namespace OAI
/-! # Physical old-image and issued-width reads from the shared chronological header -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open scoped Fin.NatCast
namespace Resident

variable {w N t l : ℕ}

def dims (S : Graph.Stage) (N t l : ℕ) : Dimensions := ⟨N,S.degree,S.colors,2^t,2^l,S.outputDegree⟩
def incoming (S : Graph.Stage) (N : ℕ) (p : Pointers) : SlotImage.Columns :=
  ⟨p.oldGraph,N*S.degree,p.oldWidths⟩
def extra (p : Pointers) : StoredColumns.Extra := ⟨p.colors,p.offsets,p.split⟩
def outgoing (S : Graph.Stage) (N t : ℕ) (p : Pointers) : SlotImage.Columns :=
  ⟨p.newGraph,N*2^t*S.outputDegree,p.newWidths⟩

/-- Word 27 is the sole mutable word among the first 34. -/
def value (x : Dimensions) (p : Pointers) (lay : Bool) (i : ℕ) : ℕ :=
  if i=selected then (if lay then 1 else 0) else headerWord x p i

/-- Raw memory equations, prior to interpreting any of the instructions. -/
structure Header (x : Dimensions) (p : Pointers) (lay : Bool) (cell : Word w) (m : Memory w) : Prop where
  pointer : (m cell.val).val=p.ownHeader
  safe : p.ownHeader+34≤2^w
  words : ∀ i : Fin 34,m (p.ownHeader+i.val)=(value x p lay i.val:Word w)

variable {x : Dimensions} {p : Pointers} {lay : Bool} {cell : Word w} {m : Memory w}

theorem Header.native (h : Header x p lay cell m) (i : Fin 34) :
    headerRead m cell i.val=(value x p lay i.val:Word w) := by
  have sum : p.ownHeader+i.val<2^w := (Nat.add_lt_add_left i.isLt _).trans_le h.safe
  have hdr : m cell.val=(p.ownHeader:Word w) := by rw [←h.pointer,Fin.cast_val_eq_self]
  change m (m cell.val + (i.val:Word w)).val=_
  rw [hdr,←Nat.cast_add,Fin.val_cast_of_lt sum]
  exact h.words i

theorem Header.field (h : Header x p lay cell m) (vs : Fin 1 → Word w) (i : Fin 34) :
    Formula.value (fun _=>cell) m vs (Template.f i.val)=(value x p lay i.val:Word w) := h.native i

theorem Header.oldColumns {S : Graph.Stage} (h : Header (dims S N t l) p lay cell m) (vs : Fin 1 → Word w) :
    Template.g.map (Formula.value (fun _=>cell) m vs) = StoredColumns.addresses (incoming S N p) (extra p) := by
  let V := Formula.value (fun _=>cell) m vs
  have f (j : ℕ) (hj : j < 34) :
      V (Template.f j)=(value (dims S N t l) p lay j : Word w) := h.field vs ⟨j,hj⟩
  have col (a n i : ℕ) :
      V (column Template.o (Template.f a) (Template.f n) i)=
      V (Template.f a)+V (Template.f n)*(i:Word w) := rfl
  have address (base i : ℕ) :
      (base : Word w) + ((N*S.degree : ℕ) : Word w) * (i : Word w) =
        ((base+N*S.degree*i : ℕ) : Word w) := by
    rw [Nat.cast_add]
    apply congrArg (fun z : Word w => (base : Word w) + z)
    apply Fin.ext
    exact (Nat.mul_mod (N*S.degree) i (2^w)).symm
  have raw (i : ℕ) : V (column Template.o (Template.f oldGraph) (Template.f oldSlots) i)=
      ((p.oldGraph+N*S.degree*i:ℕ):Word w) := by
    rw [col,f oldGraph (by decide),f oldSlots (by decide)]
    exact address p.oldGraph i
  have spl (i : ℕ) : V (column Template.o (Template.f splitShifts) (Template.f oldSlots) i)=
      ((p.split+N*S.degree*i:ℕ):Word w) := by
    rw [col,f splitShifts (by decide),f oldSlots (by decide)]
    exact address p.split i
  let rc (i : ℕ) := V (column Template.o (Template.f oldGraph) (Template.f oldSlots) i)
  let sc (i : ℕ) := V (column Template.o (Template.f splitShifts) (Template.f oldSlots) i)
  change (⟨⟨V (Template.f colors),V (Template.f offsets),rc 0,sc 2,sc 3,rc 3,rc 4,sc 6,sc 7⟩,
    sc 0,sc 1,sc 4,sc 5⟩:ArcColumns (Word w))=_
  simp only [rc,sc,raw,spl]
  rw [f colors (by decide),f offsets (by decide)]
  rfl

theorem Header.radices {S : Graph.Stage} (h : Header (dims S N t l) p lay cell m) (vs : Fin 1 → Word w) :
    (radices Template.o Template.ptr S).map (Formula.value (fun _=>cell) m vs) =
      Graph.rowRadices (w:=w) (t:=t) (l:=l) S := by
  change (⟨Formula.value (fun _=>cell) m vs (Template.f tags),
    Formula.value (fun _=>cell) m vs (Template.f remaining),
    ((2^S.colors : ℕ) : Word w), (S.degree : Word w)⟩ : Radices (Word w)) = _
  rw [show Formula.value (fun _=>cell) m vs (Template.f tags)=((2^t:ℕ):Word w) from h.field vs 15,
      show Formula.value (fun _=>cell) m vs (Template.f remaining)=((2^l:ℕ):Word w) from h.field vs 14]
  rfl


end Resident
end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage

end OAI
