import OAI.Computability.BorderVNP.TransmissionDataKeys
import OAI.Computability.BorderVNP.TransmissionDataSlabs

/-! # Absolute cell-bank addresses of the true compacted demands -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory

open Function

/-- An actual bit of the compacted output of the public placement scan. -/
abbrev Layout.PopulatedBit (d : Layout) (pp lp : ℕ → ℕ × ℕ) :=
  (i : Fin (d.directory pp lp).length) × Fin ((d.directory pp lp)[i.val]).width

/-- Forget only the compression of empty rows. The bit number within the row
is retained unchanged. -/
def Layout.rawBit (d : Layout) (pp lp : ℕ → ℕ × ℕ)
    (b : d.PopulatedBit pp lp) : d.CandidateBit pp lp :=
  ⟨d.populatedIndex pp lp b.1, ⟨b.2.val, by simpa only [← d.populatedRow pp lp] using b.2.isLt⟩⟩

private theorem rawBit_injective (d : Layout) (pp lp : ℕ → ℕ × ℕ) :
    Injective (d.rawBit pp lp) := by
  rintro ⟨i,k⟩ ⟨i',k'⟩ e
  obtain rfl : i = i' := (d.populatedIndex pp lp).injective (congrArg Sigma.fst e)
  exact congrArg (Sigma.mk i) (Fin.ext (congrArg (fun x : d.CandidateBit pp lp => x.2.val) e))

/-- Absolute destination of one packed demand lane in fixed-stride cell banks. -/
def Layout.deliveredAt (d : Layout) (pp lp : ℕ → ℕ × ℕ) (origin stride : ℕ)
    (b : d.PopulatedBit pp lp) : ℕ :=
  let r := (d.directory pp lp)[b.1.val]
  origin+r.cell*stride+r.slot+b.2.val

/-- The frame's private and live placement entries refer to distinct logical words
of the full supplied-input bank. Its prefix offsets may include other supplied words
that do not occur in this delivery directory. -/
structure BankPlacement (d : Layout) (pp lp : ℕ → ℕ × ℕ) (A : Type*) [Fintype A]
    {cells : ℕ} (cell : A → Fin cells) (id : A ↪ ℕ) (width : A → ℕ) where
  /-- Public supplied-word index corresponding to each private description or live-site word. -/
  key : d.DestinationKey ↪ A
  /-- The true number of private or live slots at each supplied word. -/
  width_eq : ∀ k, width (key k) = d.keyWidth k
  /-- The addressed physical placement table gives its actual owner and prefix displacement. -/
  entry : ∀ k, d.keyPlacement pp lp k =
    ((cell (key k)).val, DataSlabs.base cell id width (key k))

namespace BankPlacement

variable {d : Layout} {pp lp : ℕ → ℕ × ℕ} {A : Type*} [Fintype A] {cells : ℕ}
    {cell : A → Fin cells} {id : A ↪ ℕ} {width : A → ℕ}
    (place : BankPlacement d pp lp A cell id width)

/-- Send the logical word and lane to its actual typed bank index. -/
def slot (x : d.DestinationSlot) : (a : A) × Fin (width a) :=
  ⟨place.key x.1, x.2.cast (place.width_eq x.1).symm⟩

private theorem slot_injective : Injective place.slot := by
  rintro ⟨a,k⟩ ⟨b,j⟩ e
  obtain rfl : a = b := place.key.injective (congrArg Sigma.fst e)
  exact congrArg (Sigma.mk a) (Fin.ext (congrArg (fun x : (a : A) × Fin (width a) => x.2.val) e))

/-- The lowered absolute destination equals the injective typed slab address of the
private or live bit recovered from the true source candidate. -/
theorem deliveredAt_eq (bound : d.DestinationBounds) (origin stride : ℕ) (b : d.PopulatedBit pp lp) :
    d.deliveredAt pp lp origin stride b = DataSlabs.address cell id width origin stride
      (place.slot (d.destinationKey pp lp bound (d.rawBit pp lp b))) := by
  let x := d.rawBit pp lp b
  let y := d.destinationKey pp lp bound x
  have row := d.populatedRow pp lp b.1
  obtain ⟨hc,hl⟩ := d.destinationKey_placement pp lp bound x
  change (d.row pp lp x.1).cell = (d.keyPlacement pp lp y.1).1 at hc
  change (d.row pp lp x.1).slot+b.2.val = (d.keyPlacement pp lp y.1).2+y.2.val at hl
  rw [place.entry] at hc hl
  change origin+((d.directory pp lp)[b.1.val]).cell*stride+((d.directory pp lp)[b.1.val]).slot+b.2.val =
    origin+(cell (place.key y.1)).val*stride+DataSlabs.base cell id width (place.key y.1)+y.2.val
  rw [congrArg Row.cell row, congrArg Row.slot row]
  change origin+(d.row pp lp x.1).cell*stride+(d.row pp lp x.1).slot+b.2.val = _
  rw [hc, Nat.add_assoc, hl, ← Nat.add_assoc]

include place

/-- Distinct populated data slots never overwrite each other, including demands split
at a processor or site boundary. -/
theorem deliveredAt_injective (bound : d.DestinationBounds) (origin stride : ℕ)
    (room : ∀ c, DataSlabs.size cell width c ≤ stride) : Injective (d.deliveredAt pp lp origin stride) := by
  intro x y eq
  rw [place.deliveredAt_eq bound, place.deliveredAt_eq bound] at eq
  exact rawBit_injective d pp lp ((d.destinationKey_injective pp lp bound)
    (place.slot_injective (DataSlabs.address_injective cell id width origin stride room eq)))

/-- Every actual delivery lane lies below the end of the complete allocated data bank. -/
theorem deliveredAt_lt (bound : d.DestinationBounds) (origin stride : ℕ)
    (room : ∀ c, DataSlabs.size cell width c ≤ stride) (x : d.PopulatedBit pp lp) :
    d.deliveredAt pp lp origin stride x < origin+cells*stride := by
  rw [place.deliveredAt_eq bound]
  generalize place.slot (d.destinationKey pp lp bound (d.rawBit pp lp x)) = y
  obtain ⟨a,i⟩ := y
  have h := (Nat.add_lt_add_left i.isLt (DataSlabs.base cell id width a)).trans_le
    ((DataSlabs.base_end_le cell id width a).trans (room _))
  have ht := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt (cell a).isLt)
  rw [Nat.succ_mul] at ht
  change origin + (cell a).val * stride + DataSlabs.base cell id width a + i.val < _
  omega

end BankPlacement
end Packing.Directory

end BorderVNP
end Computability
end OAI
