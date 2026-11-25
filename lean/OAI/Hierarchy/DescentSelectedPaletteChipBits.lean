import OAI.Hierarchy.DescentOrdinaryBornChip
import OAI.Hierarchy.DescentOrdinaryPaletteBirth

namespace OAI
/-! # Bit axes of the original newborn palette chip -/
namespace Hierarchy.DescentOrdinaryPaletteBirth
open DescentRawCablePanel DescentSIMDLookup DescentOrdinaryBorn DescentSixParty
open scoped Classical
noncomputable section
variable {F : Type} [Field F]

/-- The newborn book stores just four dimensions of the full donor shape. The
read preserves the actual paid chip and both seat coordinates. -/
theorem word_of_chip (G : PoweredGadget F) (seed Z : ℕ) (op : RotorSpec) (z : ℕ)
    (book : DescentOrdinaryBorn.Chart) (fmt : DepotRAM.Shape)
    (blocks : book.blocks=fmt.blocks) (cap : book.cap=fmt.cap)
    (names : book.names=fmt.names) (widths : book.widths=fmt.widths)
    (chip : Cell book.chipBits) (raw : Cell (DepotRAM.outputBits fmt)) (read : chip.val=raw.val)
    (x : Fin book.blocks) (t : Fin book.cap) (party : Fin 6) :
    word G seed Z op z (chipDonor book.format chip (finProdFinEquiv (x,t))) party=
      word G seed Z op z (chipDonor fmt raw (finProdFinEquiv (x.cast blocks,t.cast cap))) party :=by
  rcases book with ⟨n,c,nm,wd,bits,args,hosts,groups,lanes,grain,scale,demand⟩
  rcases fmt with ⟨m,degree,cap₀,small,nm₀,wd₀⟩
  dsimp only at blocks cap names widths
  subst m;subst cap₀;subst nm₀;subst wd₀
  have same : chip=raw:=Fin.ext read
  subst raw
  rfl

end
end Hierarchy.DescentOrdinaryPaletteBirth

end OAI
