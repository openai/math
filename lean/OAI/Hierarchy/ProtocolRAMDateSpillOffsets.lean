import OAI.Hierarchy.TaggedWideDatedControls
import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.ProtocolRAMCheapCode
import OAI.Hierarchy.ProtocolRAMSchedule
import OAI.Hierarchy.ProbeStageProgramSize

namespace OAI
/-! # Dated spill-only prefix tables in the order of the original rows -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open ProbeStage.CoreBoard.HistoryRoles
open scoped Fin.CommRing Classical

/-- The native source and destination headers may use different row numbers from
the chronological oracle route; each queries its own original ordered local slots. -/
structure Side (D : ℕ) where
  rows : ℕ
  columns : Fin D→LocalPrefix.Columns
  ordinal : Expr
  opposite : Expr

def Side.atRole {D : ℕ} (rows original spillStart sites bits : ℕ) (stride : Bank)
    (site ordinal opposite : Expr) : Side D :=
  ⟨rows,SiteControls.columns original spillStart sites bits stride site,ordinal,opposite⟩

def Side.prefix {D : ℕ} (s : Side D) : Expr :=
  LocalPrefix.expr s.columns ⟨s.ordinal,s.opposite,.lit 1⟩

/-- Two consecutively allocated banks. Each bank reserves its actual dyadic extent,
including any trailing padding required by the physical lookup instruction. -/
structure Layout where
  first : ℕ
  oldRows : ℕ
  newRows : ℕ

def Layout.oldOffset (p : Layout) : Bank := RoleROM.bank p.first p.oldRows
def Layout.newOffset (p : Layout) : Bank := RoleROM.bank (p.first+p.oldOffset.size) p.newRows
def Layout.endAt (p : Layout) : ℕ := p.newOffset.base+p.newOffset.size

variable {W D : ℕ} (l : Layout)

def Layout.program (w : ℕ) (old new : Side D) : Procedure w :=
  (scan w l.oldOffset.base l.oldRows old.prefix).seq (scan w l.newOffset.base l.newRows new.prefix)

def Layout.time (old new : Side D) : ℕ :=
  (4+l.oldRows*(2*old.prefix.work+4))+(4+l.newRows*(2*new.prefix.work+4))

def Layout.result (old new : Side D) (m : Memory W) : Memory W :=
  image l.newOffset.base l.newRows new.prefix (image l.oldOffset.base l.oldRows old.prefix m)

theorem Layout.cheap (w : ℕ) (old new : Side D) : CheapCode (l.program w old new) :=
  @cheap_seq w (scan w l.oldOffset.base l.oldRows old.prefix) (scan w l.newOffset.base l.newRows new.prefix)
    (@scan_cheap _ _ _ _) (@scan_cheap _ _ _ _)

theorem Layout.text (w : ℕ) (old new : Side D) :
    ProbeStage.Native.text (l.program w old new)=22+4*(old.prefix.work+new.prefix.work) := by
  unfold Layout.program
  rw [ProbeStage.Native.text_seq]
  obtain ⟨a,b,c⟩:=scan_size w l.oldOffset.base l.oldRows old.prefix
  obtain ⟨e,f,g⟩:=scan_size w l.newOffset.base l.newRows new.prefix
  dsimp only [ProbeStage.Native.text]
  omega

private theorem old_le : l.oldOffset.base+l.oldRows≤l.newOffset.base :=
  Nat.add_le_add_left (ProtocolRAMPurchaseSampler.lt_span _).le _

private theorem new_le : l.newOffset.base+l.newRows≤l.endAt :=
  Nat.add_le_add_left (ProtocolRAMPurchaseSampler.lt_span _).le _

theorem Layout.exec (old new : Side D) (m : Memory W)
    (oldFit : old.prefix.Fits W l.first) (newFit : new.prefix.Fits W l.first)
    (room : l.endAt<2^W) :
    (l.program W old new).Exec m (l.result old new m) (l.time old new) := by
  have lo:=old_le l
  have hi:=new_le l
  have before : l.first≤l.newOffset.base := by change l.first≤l.first+l.oldOffset.size;omega
  let middle := image l.oldOffset.base l.oldRows old.prefix m
  have oldRun : (scan W l.oldOffset.base l.oldRows old.prefix).Exec m middle
      (4+l.oldRows*(2*old.prefix.work+4)) :=
    scan_exec l.oldOffset.base l.oldRows old.prefix m oldFit (by omega)
  have newRun : (scan W l.newOffset.base l.newRows new.prefix).Exec middle (l.result old new m)
      (4+l.newRows*(2*new.prefix.work+4)) :=
    scan_exec l.newOffset.base l.newRows new.prefix middle
      (ProtocolRAMGeneratedWrite.fits_mono _ before newFit) (by omega)
  intro P R K M pc reg pub exit rom data cfg raw entry eq
  exact Procedure.Exec.then oldRun newRun M pc reg pub exit rom data cfg raw entry eq

theorem Layout.old_read (old new : Side D) (m : Memory W) (i : Fin l.oldRows)
    (room : l.endAt<2^W) :
    l.oldOffset.read (l.result old new m) (i.val:Word W)=old.prefix.eval m (i.val:Word W) := by
  have lo:=old_le l
  have hi:=new_le l
  have fit : i.val<2^W:=by have:=i.isLt;omega
  change l.result old new m (l.oldOffset.base+(i.val:Word W).val%l.oldOffset.size)=_
  have inBank : i.val < l.oldOffset.size := i.isLt.trans (ProtocolRAMPurchaseSampler.lt_span _)
  rw [Fin.val_cast_of_lt fit,Nat.mod_eq_of_lt inBank]
  unfold Layout.result
  rw [ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl (by have:=i.isLt;omega))]
  exact ProtocolRAMGeneratedWrite.read_image _ _ _ _ i

theorem Layout.new_read (old new : Side D) (m : Memory W) (i : Fin l.newRows)
    (fit : new.prefix.Fits W l.first) (room : l.endAt<2^W) :
    l.newOffset.read (l.result old new m) (i.val:Word W)=new.prefix.eval m (i.val:Word W) := by
  have hi:=new_le l
  have word : i.val<2^W:=by have:=i.isLt;omega
  change l.result old new m (l.newOffset.base+(i.val:Word W).val%l.newOffset.size)=_
  have inBank : i.val < l.newOffset.size := i.isLt.trans (ProtocolRAMPurchaseSampler.lt_span _)
  rw [Fin.val_cast_of_lt word,Nat.mod_eq_of_lt inBank]
  unfold Layout.result
  exact (ProtocolRAMGeneratedWrite.read_image _ _ _ _ i).trans
    (eval_below new.prefix _ m _ fit (fun a ha=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl ha)))

theorem Layout.frame (old new : Side D) (m : Memory W) (i : ℕ) (out : i<l.first ∨ l.endAt≤ i) :
    l.result old new m i=m i := by
  have lo:=old_le l
  have hi:=new_le l
  change i<l.oldOffset.base ∨ l.endAt≤ i at out
  unfold Layout.result
  rw [ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega),
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega)]

end Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
end

end OAI
