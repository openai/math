import OAI.Hierarchy.DescentDonorChipLookup
import OAI.Hierarchy.DescentMaskedColumn

namespace OAI
/-! # Compile the real ordinary donor gather into the newborn argument chip -/

namespace Hierarchy.DescentOrdinaryBirthChip
open DescentRawCablePanel DescentSIMDLookup
open DescentPackedColony Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

structure Layout where
  format : DepotRAM.Shape
  hosts : ℕ
  groups : ℕ
  lanes : ℕ
  profile : ℕ
  demand : ℕ
  slots : ℕ

namespace Layout
variable (L : Layout)
local notation "a" => DepotRAM.totalBits L.format
local notation "b" => DepotRAM.outputBits L.format
def rule := DepotRAM.output L.format L.format.cap L.profile L.demand L.slots

def column : DescentMaskedColumn.Layout :=
  ⟨a,b,L.hosts,L.groups,L.lanes,L.rule⟩

abbrev rows := L.column.rows
abbrev words := L.column.words
abbrev result (base : ℕ) := L.column.result base
abbrev bank (base : ℕ) := L.column.bank base
abbrev finish (base : ℕ) := L.column.finish base
abbrev banks (base : ℕ) (src : Bank) := L.column.banks base src
abbrev program (w base : ℕ) (src : Bank) := L.column.program w base src
abbrev image {w} (base : ℕ) (src : Bank) (m : Memory w) := L.column.image base src m
abbrev ticks := L.column.ticks
abbrev phase (base : ℕ) (src : Bank) (w : ℕ) := L.column.phase base src w

theorem text (w base : ℕ) (src : Bank) :
    DescentStaticWordColumn.names (L.program w base src)=15*(L.words+1)+91 := L.column.text w base src

theorem cheap (w base : ℕ) (src : Bank) : CheapCode (L.program w base src) := L.column.cheap w base src

theorem allocation (base : ℕ) : base+L.words≤L.result base ∧ L.result base+L.rows≤L.finish base := L.column.allocation base

theorem fits {w} (base : ℕ) (src : Bank) (early : src.base+src.size≤base) (capacity : L.rows≤ src.size)
    (packed : L.lanes*max a b≤w/2) (end_ : L.finish base<2^w) :
    Fits (L.banks base src) a b L.lanes L.hosts L.groups w (L.result base) := L.column.fits base src early capacity packed end_

theorem framed {w} (base : ℕ) (src : Bank) (m : Memory w) (early : src.base+src.size≤base)
    (capacity : L.rows≤ src.size) (packed : L.lanes*max a b≤w/2) (end_ : L.finish base<2^w) :
    (L.phase base src w).Runs m ∧ ∀i,i<base ∨ L.finish base ≤ i → (L.phase base src w).image m i=m i :=
  L.column.framed base src m early capacity packed end_

theorem any {w} (base : ℕ) (src : Bank) (m : Memory w) (early : src.base+src.size≤base)
    (capacity : L.rows≤ src.size) (packed : L.lanes*max a b≤w/2) (end_ : L.finish base<2^w) :
    (L.phase base src w).Runs m :=(L.framed base src m early capacity packed end_).1

theorem reads {w} (base : ℕ) (src : Bank) (m : Memory w) (early : src.base+src.size≤base)
    (capacity : L.rows≤ src.size) (packed : L.lanes*max a b≤w/2) (end_ : L.finish base<2^w)
    (parts : Fin L.hosts→Fin L.groups→DepotRAM.Parts L.format)
    (prior : Reads src (fun h g=>DepotRAM.combine L.format (parts h g)) L.lanes m) :
    Reads (L.bank base) (fun h g=>DepotRAM.chip L.format L.format.cap L.profile L.demand L.slots (parts h g))
      L.lanes ((L.phase base src w).image m) :=by
  have rows_eq : (fun (h : Fin L.hosts) (g : Fin L.groups) =>
      L.column.rule (DepotRAM.combine L.format (parts h g))) =
      (fun h g=>DepotRAM.chip L.format L.format.cap L.profile L.demand L.slots (parts h g)) := by
    funext h g
    exact congrArg (DepotRAM.chip L.format L.format.cap L.profile L.demand L.slots)
      (DepotRAM.separate_combine L.format (parts h g))
  rw [←rows_eq]
  exact L.column.reads base src m early capacity packed end_ (fun h g=>DepotRAM.combine L.format (parts h g)) prior

theorem tariff (w base : ℕ) (src : Bank) :
    L.ticks+7*DescentStaticWordColumn.names (L.program w base src)=750+115*L.words+44*L.rows := L.column.tariff w base src

theorem half_page (h : ℕ) (pitch : a*L.lanes≤h/2) : L.words≤2^(h/2)+L.rows := L.column.half_page h pitch

theorem end_space (base h : ℕ) (pitch : a*L.lanes≤h/2) :
    L.finish base≤base+2^(h/2)+4*L.rows+4 := L.column.end_space base h pitch

theorem charged (h w base : ℕ) (src : Bank) (pitch : a*L.lanes≤h/2) :
    L.ticks+7*DescentStaticWordColumn.names (L.program w base src)≤
      750+115*2^(h/2)+159*L.rows := L.column.charged h w base src pitch
end Layout
end
end Hierarchy.DescentOrdinaryBirthChip

end OAI
