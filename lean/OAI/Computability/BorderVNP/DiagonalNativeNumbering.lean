import OAI.Computability.BorderVNP.CubePhysicalRoutedTallies
import OAI.Computability.BorderVNP.DiagonalNumberedTallies

/-! # Transport of the actual selected unary slots and scalar lookup positions -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing
open scoped BigOperators Classical

variable {Team Param Gadget Team' Param' Gadget' : Type*}

/-- Number a passing pair of counter vectors. Failed local assignments keep
their rejection tag, even if the passing pair of counters would be zero. -/
noncomputable def numberEntry (param : Param ≃ Param') (scalar : Gadget ≃ Gadget') :
    Entry Param Gadget → Entry Param' Gadget' :=
  WithZero.recZeroCoe 0 fun z => passed (z.toAdd.1.mapDomain param) (z.toAdd.2.mapDomain scalar)

theorem counters_numberEntry (param : Param ≃ Param') (scalar : Gadget ≃ Gadget') (z : Entry Param Gadget) :
    counters (numberEntry param scalar z) =
      ((counters z).1.mapDomain param,(counters z).2.mapDomain scalar) := by
  induction z using WithZero.recZeroCoe with
  | zero => simp [numberEntry,counters]; rfl
  | coe z => rfl

theorem numberEntry_gadget (param : Param ≃ Param') (scalar : Gadget ≃ Gadget') (g : Gadget) :
    numberEntry param scalar (gadget g) = gadget (scalar g) := by
  change passed (Finsupp.mapDomain param 0) (Finsupp.mapDomain scalar (Finsupp.single g 1)) = _
  rw [Finsupp.mapDomain_zero,Finsupp.mapDomain_single]
  rfl

variable {D b : ℕ} {P : Type*} {bits : P → ℕ} {N : Network D P bits}

/-- Original batch, grammar-label and binary-place numbering for the true
power occurrence. Its binary place is the one used by the native reader. -/
def numberSlot (team : Team ≃ Team') (param : Param ≃ Param') :
    PowerSlot Team Param b ≃ PowerSlot Team' Param' b :=
  team.prodCongr (param.prodCongr (Equiv.refl (Fin b)))

/-- Apply the grammar and scalar numberings independently to each stored site entry. -/
noncomputable def numberTables (param : Param ≃ Param') (scalar : Gadget ≃ Gadget')
    (tags : N.Tables (Entry Param Gadget)) : N.Tables (Entry Param' Gadget') :=
  fun v e x => numberEntry param scalar (tags v e x)

namespace PowerWords

variable [Fintype Team] [Fintype Team'] [Fintype Param] [Fintype Param']
    {tags : N.Tables (Entry Param Gadget)}
    (words : PowerWords Team Param Gadget b N tags)
    (team : Team ≃ Team') (param : Param ≃ Param') (scalar : Gadget ≃ Gadget')

/-- Read exactly the same original bits and hosting sites after replacing
their external names by the finite integers used by the team RAM. -/
noncomputable def number : PowerWords Team' Param' Gadget' b N (numberTables param scalar tags) where
  site j := words.site ((numberSlot team param).symm j)
  selected v e x j := words.selected v e x ((numberSlot team param).symm j)
  located v e x j := words.located v e x _
  exact v e x := by
    change (counters (numberEntry param scalar (tags v e x))).1 = _
    rw [counters_numberEntry,words.exact,Finsupp.mapDomain_finsetSum]
    apply Fintype.sum_equiv (numberSlot team param)
    intro j
    rw [Equiv.symm_apply_apply]
    simp [slotPower,numberSlot]

theorem number_localUse (e : PowerSites.LocalEdges N) (x : PowerSites.LocalPorts N)
    (t : Team') (p : Param') (j : Fin b) :
    (words.number team param scalar).localUse e x t p j =
      words.localUse e x (team.symm t) (param.symm p) j := rfl

end PowerWords
end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
