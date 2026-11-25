import OAI.Hierarchy.DescentResetStemHostRender
import OAI.Hierarchy.DescentResetOriginalSlots
import OAI.Hierarchy.DescentOperandPairBook

namespace OAI
/-! Public code for the two oriented stem-word laws on the common original-number shelf. -/
namespace Hierarchy.DescentResetNumberStem
open DescentSIMDLookup ProtocolRAM DescentResetOriginalSlots
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
structure Layout (X J K : ℕ) where
  degree : ℕ
  k : ℕ
  depth : ℕ
  Y : ℕ
  labels : ℕ
  cap : ℕ
  links : ℕ
  pc : ℕ
  wordBits : ℕ
  field : ℕ
  M : ℕ
  rows : ℕ
  header : ℕ
  original : ℕ
  shelf : Fin J↪Fin K
  side : Fin J→Bool
  src : Fin X→Fin J→Fin 6→Expr

namespace Layout
variable {X J K w : ℕ} (L : Layout X J K)
def laws : DescentOperandPairBook.Laws 6 L.field L.wordBits :=
  DescentResetStemWord.withHost L.degree L.k L.depth L.Y L.labels L.cap L.links L.pc L.wordBits
def term (p : Fin (X*J)) :=
  let q:=finProdFinEquiv.symm p
  DescentOperandPairBook.expr L.laws L.M L.header (L.side q.2) (L.src q.1 q.2)
def jobs:=passes L.shelf L.original L.rows L.term
def code (w : ℕ) :=(DescentOperandPairBook.program L.laws L.M w L.header).seq (program w L.jobs)
def ticks:=(4+10*DescentOperandPairBook.words 6 L.field L.M)+clock L.jobs
def image (m : Memory w) := result L.jobs (DescentOperandPairBook.memory L.laws L.M L.header m)
def headerEnd:=L.header+DescentOperandPairBook.words 6 L.field L.M
def endAddress:=finish L.original L.rows X K

structure Room (w : ℕ) : Prop where
  input : ∀x j t,(L.src x j t).Fits w L.header
  separate : L.headerEnd≤L.original
  fits : L.endAddress<2^w

theorem range {X J K : ℕ} (shelf : Fin J↪Fin K) (start rows : ℕ) (p : Fin (X*J)) :
    start+(cell shelf p).val*stride rows+rows≤finish start rows X K := by
  have idx:=Nat.mul_le_mul_right (stride rows) (cell shelf p).isLt
  rw [Nat.succ_mul] at idx
  have cap:rows≤ stride rows:=Nat.le_pow_clog (by decide) _
  unfold finish;omega

theorem any (r : L.Room w) (m : Memory w) :
    (L.code w).Exec m (L.image m) L.ticks ∧ CheapCode (L.code w) ∧
    ∀i,i<L.header ∨ L.endAddress≤ i→L.image m i=m i := by
  have before:L.original≤L.endAddress:=Nat.le_add_right ..
  have room:=r.separate.trans_lt (before.trans_lt r.fits)
  have fit (p : Fin (X*J)) : (L.term p).Fits w L.original :=
    ProtocolRAMGeneratedWrite.fits_mono _ r.separate (DescentOperandPairBook.expr_fits L.laws _ L.header _ (r.input _ _) room)
  obtain ⟨mount,_,_,old,cheap⟩:=DescentOperandPairBook.mounted L.laws L.M L.header m room
  have safe:=DescentResetOriginalSlots.safe L.shelf L.original L.rows L.term fit r.fits
  refine ⟨mount.then (program_exec _ _ safe),cheap_seq cheap (@ProtocolRAM.program_cheap _ _),?_⟩
  have low:L.header≤L.headerEnd:=Nat.le_add_right ..
  intro z away
  apply (DescentResetOriginalSlots.frame L.shelf L.original L.rows L.term _ z ?_).trans
  · apply old
    rcases away with lo|hi
    · exact .inl lo
    · exact .inr (r.separate.trans (before.trans hi))
  · intro p
    rcases away with lo|hi
    · exact .inl ((lo.trans_le (low.trans r.separate)).trans_le (Nat.le_add_right ..))
    · exact .inr ((range L.shelf L.original L.rows p).trans hi)

end Layout
end
end Hierarchy.DescentResetNumberStem

end OAI
