import OAI.Hierarchy.DescentDatedPrimitiveExtent
import OAI.Hierarchy.DescentOrdinaryPaletteProgram
import OAI.Hierarchy.DescentOrdinaryPaletteBirthBook
import OAI.Hierarchy.DescentDatedWOrigin
import OAI.Hierarchy.DescentOrdinaryAfterSigned
import OAI.Hierarchy.DescentDatedOrdinaryCountRoof

namespace OAI
/-! The dated primitive updater uses the old halo, the real donor chip, and the already returned origin. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryPrimitiveCheckpoint ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
set_option quotPrecheck false
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ)
  (A : ArgumentEntry v) («matching» : A.Match v floor) (radix : v.vector.radix=2^v.reference.k)
local notation "L" => v.paletteShape
local notation "oldEnd" => v.operandEnd floor
local notation "base" => v.primitiveFirst oldEnd
local notation "bound" => v.primitiveRoof oldEnd
local notation "G" => v.gadget
local notation "s" => v.palette.seedWidth
local notation "Z" => v.palette.grainLimit
local notation "op" => v.palette.rotor

include «matching» in
private theorem birthFields : (L).fields=DescentOrdinaryPaletteBirth.fields v.bornBook:=by
  change 2^v.reference.k*v.reference.capacity*6=v.bornBook.blocks*v.bornBook.cap*6
  rw [«matching».newBlocks,«matching».newCap]

def primitiveSources : (L).Inputs where
  previous x := A.labels v floor (x.cast «matching».oldBlocks.symm)
  newborn e := DescentOrdinaryPaletteBirth.bank v.bornBook oldEnd (e.cast (birthFields v floor A «matching»))
  origin x := v.originBank floor (x.cast radix.symm)
  halo := (A.ports v floor).roster

def primitiveBirth (w : ℕ) :=DescentOrdinaryPaletteBirth.phase G s Z op v.bornBook (A.chipBank v floor) oldEnd w
def primitiveUpdate (w : ℕ) : NativePhase w :=
  (v.primitiveBirth floor A w).seq ((L).phase base (v.primitiveSources floor A «matching» radix) w)

structure PrimitiveRoom (w : ℕ) : Prop where
  past : ∀x,(A.labels v floor x).Fits w oldEnd
  chip : (A.chipBank v floor).Fits w oldEnd
  origin : ∀x,(v.originBank floor x).Fits w oldEnd
  halo : (A.ports v floor).roster.Fits w oldEnd
  cells : (L).hosts*(L).ports≤(A.ports v floor).roster.size
  space : bound<2^w

include radix in
theorem primitive_run {w : ℕ} (fits : v.PrimitiveRoom floor A w) :
    Layout.Keep (v.primitiveUpdate floor A «matching» radix w) oldEnd bound:=by
  have begin_ : oldEnd≤base:=(DescentOrdinaryPaletteBirth.order v.bornBook oldEnd).1.trans
    (DescentOrdinaryPaletteBirth.order v.bornBook oldEnd).2
  have after_ : base≤bound:=by rw [primitiveRoof, (L).translated];exact Nat.le_add_right ..
  have birth : Layout.Keep (v.primitiveBirth floor A w) oldEnd base:=fun m=>
    DescentOrdinaryPaletteBirth.any G s Z op v.bornBook (A.chipBank v floor) oldEnd m fits.chip (after_.trans_lt fits.space)
  have move {b : Bank} (hb : b.Fits w oldEnd) : b.Fits w base:=⟨hb.1,hb.2.1,hb.2.2.trans begin_⟩
  have ready_ : (L).Early base (v.primitiveSources floor A «matching» radix) w:=
    ⟨fun x=>move (fits.past _),fun j=>(DescentOrdinaryPaletteBirth.placed v.bornBook oldEnd (after_.trans_lt fits.space) _).1,
     fun x=>move (fits.origin _),move fits.halo,fits.cells⟩
  exact birth.seq ((L).any base _ ready_ fits.space) begin_ after_

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
