import OAI.ThreeFlat.Diagonal.CompressorPostImage

namespace OAI
/-! # Exact source, field and lane ordinals for the three real output scans -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.PostImage
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.DescriptorScan
open scoped Fin.NatCast
variable {B L A : Type*} {d N Z w count : ℕ}

def slotNumbers (b : B ≃ Fin N) : (B × Fin d) ≃ Fin (N*d) :=
  (b.prodCongr (Equiv.refl _)).trans finProdFinEquiv

def fieldNumbers : (Bool × Fin 3) ≃ Fin 6 := (finTwoEquiv.symm.prodCongr (Equiv.refl _)).trans finProdFinEquiv

def graphNumbers (b : B ≃ Fin N) : (Bool × Fin 3) × (B × Fin d) ≃ Fin (6*(N*d)) :=
  (fieldNumbers.prodCongr (slotNumbers b)).trans finProdFinEquiv

def edgeNumbers (b : B ≃ Fin N) (lane : L ≃ Fin Z) : SlotImage.Edge B L d ≃ Fin (N*d*Z) :=
  ((slotNumbers b).prodCongr lane).trans finProdFinEquiv

theorem slotNumbers_val (b : B ≃ Fin N) (p : B × Fin d) :
    (slotNumbers b p).val=SlotImage.ordinal b p := by change _+_*_=_*_+_; ac_rfl

theorem fieldNumbers_val (back : Bool) (f : Fin 3) :
    (fieldNumbers (back,f)).val=SlotImage.column back f := by
  cases back <;> change _ + 3 * _ = _ + _ <;> simp [finTwoEquiv]; omega

theorem graphNumbers_val (b : B ≃ Fin N) (p : B × Fin d) (rev : Bool) (f : Fin 3)
    (C : SlotImage.Columns) (hc : C.rows=N*d) :
    C.graph + (graphNumbers b ((rev,f),p)).val=SlotImage.cell C b p rev f := by
  change C.graph+((slotNumbers b p).val+(N*d)*(fieldNumbers (rev,f)).val)=_
  rw [slotNumbers_val,fieldNumbers_val]
  unfold SlotImage.cell
  rw [hc]
  omega

theorem edgeNumbers_val (b : B ≃ Fin N) (lane : L ≃ Fin Z) (e : SlotImage.Edge B L d) :
    (edgeNumbers b lane e).val=SlotImage.edgeOrdinal b lane e := by
  change (lane e.2).val+Z*(slotNumbers b e.1).val=_
  rw [slotNumbers_val]
  unfold SlotImage.edgeOrdinal
  ac_rfl

def file (number : A ≃ Fin count) (word : A → Word w) (start addr : ℕ) : Word w :=
  if hi : addr-start<count then word (number.symm ⟨addr-start,hi⟩) else 0

@[simp] theorem file_at (number : A ≃ Fin count) (word : A → Word w) (start : ℕ) (a : A) :
    file number word start (start+(number a).val) = word a := by
  simp [file,(number a).isLt]

/-- A typed, once-only enumeration suffices to discharge *every* in-range
address checked by the physical native span. -/
theorem file_spec (current : Word w) (pub : Fin 1 → Word w) (f : Template.F)
    (lo len : ℕ) (m : Memory w) (start : ℕ) (number : A ≃ Fin count) (word : A → Word w)
    (fit : start+count<2^w) (hlo : (headerRead m current lo).val=start)
    (hlen : (headerRead m current len).val=count)
    (typed : ∀ a : A,∀ alt,agreesOutside start (start+count) alt m →
      (Template.emit current f).eval pub alt (fun _=>((start+(number a).val:ℕ):Word w))=word a) :
    FileSpec current pub f lo len m start count (file number word start) where
  fit := fit
  lowWord := hlo
  lenWord := hlen
  values address alt left right frame := by
    let i : Fin count := ⟨address.val-start,by omega⟩
    let a := number.symm i
    have pos : start+(number a).val=address.val := by simp [a,i,Nat.add_sub_of_le left]
    have cast : ((start+(number a).val:ℕ):Word w)=address := by rw [pos,Fin.cast_val_eq_self]
    rw [←pos,file_at]
    simpa only [cast] using typed a alt frame

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.PostImage

end OAI
