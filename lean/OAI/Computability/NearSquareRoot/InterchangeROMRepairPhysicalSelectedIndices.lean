import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalCorrectionLeaf
import OAI.Computability.NearSquareRoot.ScheduleGeneratorFunction

/-! The recorded order of the two sign-correction blocks. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.Selected

open IntegerMultiplication IntegerMultiplication.Strip InterchangeROMTable

/-- Each label contributes its ground check rows consecutively. -/
def checkSeries (l s : ℕ) : Series (Fin l × Fin s) :=
  (Series.natural (l*s)).via finProdFinEquiv.symm

/-- The first block is the value at the false selector. -/
def indices (l s : ℕ) : List CheckIndex :=
  let block (b : Bool) := (List.range (l*s)).map fun i => (b,i/s,i%s)
  block false ++ block true

theorem indices_typed (l s : ℕ) :
    (Correction.twoBlocks (checkSeries l s)).tab (checkIndex Fin.val) = indices l s := by
  simp only [Correction.twoBlocks, Series.tab, checkSeries, Series.via, Series.natural, Series.fixed,
    List.map_append, List.map_map, indices]
  have h : (List.finRange (l*s)).map Fin.val = List.range (l*s) := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp
  rw [← h]
  simp only [List.map_map]
  rfl

theorem computable_indices {X : Type} [Primcodable X] {l s : X → ℕ}
    (hl : Computable l) (hs : Computable s) : Computable (fun x => indices (l x) (s x)) := by
  have h (b : Bool) : Computable fun x =>
      (List.range (l x*s x)).map fun i => (b,i/s x,i%s x) :=
    Generator.computable_rangeMap (Primrec.nat_mul.to_comp.comp hl hs)
      ((Computable.const b).pair ((Primrec.nat_div.to_comp.comp Computable.snd (hs.comp Computable.fst)).pair
        (Primrec.nat_mod.to_comp.comp Computable.snd (hs.comp Computable.fst)))).to₂
  exact Primrec.list_append.to_comp.comp (h false) (h true)

end InterchangeROMRepair.Physical.Selected

end NearSquareRoot
end Computability
end OAI
