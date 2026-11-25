import OAI.Hierarchy.DescentDatedPrimitiveRead

namespace OAI
/-! Original matched first-grain and party number of every published ordinary
primitive birth in the retained role archive. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryPrimitiveCheckpoint DescentPackedColony DescentSIMDLookup DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ)
  (A : ArgumentEntry v) («matching» : A.Match v floor) (radix : v.vector.radix=2^v.reference.k)
local notation "L" => v.paletteShape
local notation "src" => v.primitiveSources floor A «matching» radix
local notation "oldEnd" => v.operandEnd floor
local notation "base" => v.primitiveFirst oldEnd
local notation "G" => v.gadget
local notation "s" => v.palette.seedWidth
local notation "Z" => v.palette.grainLimit
local notation "op" => v.palette.rotor

variable (past : Fin v.paletteShape.blocks→Fin v.paletteShape.hosts→Fin v.paletteShape.oldGroups→Cell (v.paletteShape.primitiveBits*v.paletteShape.oldNodes))
    (chip : Fin v.bornBook.hosts→Fin v.bornBook.groups→Cell v.bornBook.chipBits)
    (hosts : v.paletteShape.hosts=v.bornBook.hosts) (groups : v.paletteShape.oldGroups=v.bornBook.groups)
    (origin : Fin v.paletteShape.blocks→Fin v.paletteShape.successors→Fin v.paletteShape.groups→Cell (v.paletteShape.originBits*v.paletteShape.newNodes))
    (next : Fin v.paletteShape.hosts→Fin v.paletteShape.ports→Option (Fin v.paletteShape.hosts))

open DescentOrdinaryPaletteBirth DescentOrdinaryBorn DescentPrimitivePalette
/-- The cast from reference widths to birth widths preserves the actual two
physical donor indices and party. -/
theorem palette_birth_at (x : Fin v.paletteShape.blocks) (t : Fin v.paletteShape.capacity) (who : Fin 6)
    (h : Fin v.paletteShape.hosts) (g : Fin v.paletteShape.oldGroups) :
    let site:=x.cast «matching».newBlocks.symm
    let slot:=t.cast «matching».newCap.symm
    let donor:=chipDonor v.bornBook.format (chip (h.cast hosts) (g.cast groups)) (finProdFinEquiv (site,slot))
    (v.paletteStock floor A «matching» past chip hosts groups origin next).newborn ((L).bornIndex x t who) h g=
      word G s Z op v.bornBook.scale donor who:=by
  intro site slot donor
  change published G s Z op v.bornBook (Fin.cast _ ((L).bornIndex x t who)) _=_
  have index : Fin.cast (show (L).fields=DescentOrdinaryPaletteBirth.fields v.bornBook from by
      change 2^v.reference.k*v.reference.capacity*6=v.bornBook.blocks*v.bornBook.cap*6
      rw [«matching».newBlocks,«matching».newCap])
      ((L).bornIndex x t who)=finProdFinEquiv (finProdFinEquiv (site,slot),who):=by
    apply Fin.ext
    change who.val + 6*(t.val+v.reference.capacity*x.val) =
      who.val + 6*(t.val+v.bornBook.cap*x.val)
    rw [«matching».newCap]
  rw [index]
  let xt : Fin v.bornBook.donors := finProdFinEquiv (site,slot)
  have back : ((@finProdFinEquiv v.bornBook.donors 6).symm (finProdFinEquiv (xt,who))) = (xt,who) :=
    (@finProdFinEquiv v.bornBook.donors 6).symm_apply_apply (xt,who)
  change word G s Z op v.bornBook.scale (chipDonor v.bornBook.format (chip (h.cast hosts) (g.cast groups))
    ((@finProdFinEquiv v.bornBook.donors 6).symm (finProdFinEquiv (xt,who))).1)
    ((@finProdFinEquiv v.bornBook.donors 6).symm (finProdFinEquiv (xt,who))).2 = _
  rw [back]
  rfl

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
