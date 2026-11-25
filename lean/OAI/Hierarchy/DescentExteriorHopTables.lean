import OAI.Hierarchy.DescentExteriorReplay
import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.ProtocolRAMEndpointPrefixCheap

namespace OAI
/-! # Producing the two host-ancestry tables from one reached mode word -/

namespace Hierarchy.DescentExteriorReplay
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Fin.CommRing
noncomputable section
namespace HopTables
structure Layout where
  mode : Bank
  pitches : Bank
  pointers : Bank
  shapes : Bank
  counts : ℕ

def modeAt (L : Layout) : Expr := .lookup L.mode (.lit 0)
def pitchAt (L : Layout) : Expr := .lookup L.pitches (modeAt L)
def shapeAt (L : Layout) : Expr :=
  .lookup L.shapes (.op .add (.lookup L.pointers (modeAt L)) .row)

variable {w H digits : ℕ} (L : Layout) (slot : Hop)
def pitch (m : Memory w) := ((pitchAt L).eval m 0).val
def repeated (H : ℕ) (m : Memory w) := image L.counts H (pitchAt L) m
def prefixes (H : ℕ) (m : Memory w) :=
  ProtocolRAMEndpointPrefix.image slot.hostBase.base (fun i=>i*pitch L m) (repeated L H m) H
def issued (H digits : ℕ) (m : Memory w) :=
  image slot.localShape.base digits (shapeAt L) (prefixes L slot H m)

def program (w H digits : ℕ) :=
  ((scan w L.counts H (pitchAt L)).seq
    (ProtocolRAMEndpointPrefix.exclusive w L.counts slot.hostBase.base H)).seq
    (scan w slot.localShape.base digits (shapeAt L))
def fee (H digits : ℕ) := (4+26*H+(10+(3+12*H)))+(4+42*digits)

structure Room (w H digits : ℕ) : Prop where
  pitch : (pitchAt L).Fits w L.counts
  shape : (shapeAt L).Fits w L.counts
  reserve : L.counts+H≤ slot.hostBase.base
  separate : slot.hostBase.base+H+1≤ slot.localShape.base
  ends : slot.localShape.base+digits<2^w
  hosts : H≤ slot.hostBase.size
  branches : digits≤ slot.localShape.size

theorem run (m : Memory w) (h : Room L slot w H digits) :
    (program L slot w H digits).Exec m (issued L slot H digits m) (fee H digits) ∧
      CheapCode (program L slot w H digits) := by
  let first := scan w L.counts H (pitchAt L)
  let prefixPass := ProtocolRAMEndpointPrefix.exclusive w L.counts slot.hostBase.base H
  let last := scan w slot.localShape.base digits (shapeAt L)
  have firstRoom : L.counts + H < 2^w := by
    have := h.reserve
    have := h.separate
    have := h.ends
    omega
  have prefixRoom : slot.hostBase.base + H + 1 < 2^w := by
    have := h.separate
    have := h.ends
    omega
  have addressOrder : L.counts ≤ slot.localShape.base := by
    have := h.reserve
    have := h.separate
    omega
  have a : first.Exec m (repeated L H m) (4+H*26) :=
    @scan_exec w L.counts H (pitchAt L) m h.pitch firstRoom
  have b : prefixPass.Exec (repeated L H m) (prefixes L slot H m) (10+(3+12*H)) := by
    refine @ProtocolRAMEndpointPrefix.run w L.counts slot.hostBase.base H (fun i=>i*pitch L m)
      (repeated L H m) h.reserve prefixRoom (by simp) ?_
    intro i hi
    rw [show repeated L H m (L.counts+i)=(pitchAt L).eval m (i:Word w) from
      ProtocolRAMGeneratedWrite.read_image _ _ _ _ ⟨i,hi⟩]
    change (((i+1)*((pitchAt L).eval m 0).val:ℕ):Word w)=_
    rw [Nat.succ_mul,Nat.cast_add]
    simp [pitch,pitchAt,modeAt,Expr.eval]
  have c : last.Exec (prefixes L slot H m) (issued L slot H digits m) (4+digits*42) :=
    @scan_exec w slot.localShape.base digits (shapeAt L) (prefixes L slot H m)
      (ProtocolRAMGeneratedWrite.fits_mono _ addressOrder h.shape) h.ends
  constructor
  · change ((first.seq prefixPass).seq last).Exec m (issued L slot H digits m) _
    unfold fee
    rw [Nat.mul_comm 26 H,Nat.mul_comm 42 digits]
    exact @Procedure.Exec.then w (first.seq prefixPass) last m (prefixes L slot H m)
      (issued L slot H digits m) ((4+H*26)+(10+(3+12*H))) (4+digits*42)
      (@Procedure.Exec.then w first prefixPass m (repeated L H m) (prefixes L slot H m)
        (4+H*26) (10+(3+12*H)) (@a) (@b)) (@c)
  · exact @cheap_seq w (first.seq prefixPass) last
      (@cheap_seq w first prefixPass (@scan_cheap w L.counts H (pitchAt L))
        (@ProtocolRAMRankCheap.exclusive_cheap w L.counts slot.hostBase.base H))
      (@scan_cheap w slot.localShape.base digits (shapeAt L))

private theorem bank_frame {b : Bank} {m m' : Memory w} {cut : ℕ} (fit : b.Fits w cut)
    (prev : ∀a<cut,m' a=m a) (x : Word w) : b.read m' x=b.read m x := by
  apply prev
  have small:=Nat.mod_lt x.val fit.1
  have last:=fit.2.2
  omega

theorem reads (m : Memory w) (h : Room L slot w H digits) :
    (∀i : Fin H,slot.hostBase.read (issued L slot H digits m) (i.val:Word w)=
      ((i.val*pitch L m:ℕ):Word w)) ∧
    (∀j : Fin digits,slot.localShape.read (issued L slot H digits m) (j.val:Word w)=
      (shapeAt L).eval m (j.val:Word w)) := by
  have old (a : ℕ) (lo : a<L.counts) : prefixes L slot H m a=m a := by
    rw [prefixes,ProtocolRAMEndpointPrefix.frame _ _ _ _ _ (Or.inl (by have:=h.reserve;omega))]
    simp [repeated,image,fillSegment,Nat.not_le_of_lt lo]
  constructor
  · intro i
    have hi:=i.isLt;have end_:=h.ends;have sep:=h.separate
    have addr : slot.hostBase.base+i.val<slot.localShape.base:=by omega
    change issued L slot H digits m (slot.hostBase.base+(i.val:Word w).val%_)=_
    rw [Fin.val_cast_of_lt (by omega : i.val<2^w),Nat.mod_eq_of_lt (hi.trans_le h.hosts)]
    rw [issued,show image slot.localShape.base digits (shapeAt L) (prefixes L slot H m)
      (slot.hostBase.base+i.val)=prefixes L slot H m (slot.hostBase.base+i.val) from
      by simp [image,fillSegment,Nat.not_le_of_lt addr]]
    exact ProtocolRAMEndpointPrefix.read _ _ _ _ _ hi.le
  · intro j
    have hj:=j.isLt;have end_:=h.ends
    change issued L slot H digits m (slot.localShape.base+(j.val:Word w).val%_)=_
    rw [Fin.val_cast_of_lt (by omega : j.val<2^w),Nat.mod_eq_of_lt (hj.trans_le h.branches)]
    rw [issued,ProtocolRAMGeneratedWrite.read_image _ _ _ _ j]
    have fits:=h.shape
    change L.shapes.Fits w L.counts ∧ ((L.pointers.Fits w L.counts ∧ (L.mode.Fits w L.counts ∧ True)) ∧ True) at fits
    simp only [shapeAt,modeAt,Expr.eval,bank_frame fits.2.1.2.1 old,bank_frame fits.2.1.1 old,
      bank_frame fits.1 old]

theorem selected {m : Memory w} (h : Room L slot w H digits) (sel base pitch₀ : Word w)
    (shape : Fin digits→Word w) (select : L.mode.read m 0=sel) (pitchWord : L.pitches.read m sel=pitch₀)
    (start : L.pointers.read m sel=base) (table : ∀j : Fin digits,L.shapes.read m (base+(j.val:Word w))=shape j) :
    (∀i : Fin H,slot.hostBase.read (issued L slot H digits m) (i.val:Word w)=(i.val:Word w)*pitch₀) ∧
    (∀j : Fin digits,slot.localShape.read (issued L slot H digits m) (j.val:Word w)=shape j) := by
  constructor
  · intro i
    rw [(reads L slot m h).1]
    simp [pitch,pitchAt,modeAt,Expr.eval,select,pitchWord]
  · intro j
    rw [(reads L slot m h).2]
    simpa [shapeAt,modeAt,Expr.eval,RowOp.opcode,BinaryOp.eval,select,start] using table j

end HopTables
end
end Hierarchy.DescentExteriorReplay

end OAI
