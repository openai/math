import OAI.Computability.BorderVNP.PackedRoutingPrefix
import OAI.Computability.BorderVNP.PackedBundleGroups

/-! # The physical width of the private description prefix in each receiving cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical RoutingISA
open Directory Directory.PrivateBank
open scoped Classical

variable {D s m n C e k w J A : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} {σ : Type*} [Fintype σ]
variable (N : Network D P bits) (cell : N.Site → Fin C) (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
variable (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n) (F : Fields s m n C e k w σ) {x : σ → Bool}
variable (net : Represents N cell aux siteID edgeID portID F x) (codes : ∀ c, (F.cells c).val=c.val)
variable (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)
variable (original : Fin J → N.Site) (live : Fin A → P) (frame origin desc gap : ℕ)
variable {mem : ℕ → ℕ} (image : Image F (siteID ∘ original) (portID ∘ live) x origin mem)
local notation "l" => privateLayout frame origin m C J desc gap

/-- The original supplied inputs, the one reserved gap and exactly the
descriptions assigned to this cell occupy the complete compact receiving slab. -/
theorem cell_bank_size (c : Fin C) :
    let slots := fun v : SuppliedWord N cell => v.1
    let getCell := Sum.elim (Sum.elim slots id) (cell ∘ original)
    let widths := Sum.elim (Sum.elim (supplyWidth N cell) (fun _ : Fin C => gap)) (fun _ : Fin J => desc)
    DataSlabs.size getCell widths c =
      suppliedSize N cell c+gap+DataSlabs.size (cell ∘ original) (fun _ => desc) c := by
  intro slots getCell widths
  change (∑ i, if getCell i=c then widths i else 0)=_
  rw [Fintype.sum_sum_type]
  change DataSlabs.size (Sum.elim slots id) (Sum.elim (supplyWidth N cell) (fun _ : Fin C => gap)) c + _=_
  rw [reservedSize,dataSlabs_size]
  rfl

include net codes fit image

/-- The RAM census of every final cell equals the semantic supplied widths
and the original descriptions whose retained hosts lie in this cell. -/
theorem Image.private_census (c : Fin C) :
    mem ((l).supplied+c.val)+gap+PrivatePlacement.prefixCounts ((l).owner mem) desc J c.val =
      suppliedSize N cell c+gap+DataSlabs.size (cell ∘ original) (fun _ => desc) c := by
  have facts := image.placed N cell aux siteID edgeID portID F net codes fit original live origin mem
  have owners (i : Fin J) : (l).owner mem i.val = (cell (original i)).val := by
    simpa only [privateLayout,PrivatePlacement.Layout.owner,Directory.ISA.placement,Nat.mul_comm 2 i.val]
      using congrArg Prod.fst (facts.1 i)
  have supplied : mem ((l).supplied+c.val)=suppliedSize N cell c := by
    simpa only [privateLayout,PrivatePlacement.Layout.supplied,bases,Nat.mul_comm 2 m] using facts.2.1 c
  rw [supplied]
  apply congrArg (suppliedSize N cell c + gap + ·)
  have loc (i : Fin J) : (cell ∘ original) i=c ↔ (l).owner mem i.val=c.val :=
    Fin.ext_iff.trans (by simp only [owners,Function.comp_apply])
  simp only [DataSlabs.size,loc,PrivatePlacement.prefixCounts]
  exact (Fin.sum_univ_eq_sum_range (fun i => if (l).owner mem i=c.val then desc else 0) J).symm

/-- Actual cell-wise capacity proves all native prefix pointers fit. This only
charges descriptions belonging to the currently addressed cell. -/
theorem Image.privateFit_of_census {stride : ℕ} (fr : frame+92 < 2^w)
    (ctl : mem (frame+92)+8 < 2^w) (arr : (bases origin m C J).livePairs < 2^w)
    (strideFit : stride < 2^w) (room : ∀ c, suppliedSize N cell c+gap+
      DataSlabs.size (cell ∘ original) (fun _ => desc) c ≤ stride) : (l).Fits w mem := by
  have facts := image.placed N cell aux siteID edgeID portID F net codes fit original live origin mem
  have owners (i : Fin J) : (l).owner mem i.val = (cell (original i)).val := by
    simpa only [privateLayout,PrivatePlacement.Layout.owner,Directory.ISA.placement,Nat.mul_comm 2 i.val]
      using congrArg Prod.fst (facts.1 i)
  constructor
  case frame => exact fr
  case control => exact ctl
  case owners => intro i hi; exact (owners ⟨i,hi⟩).trans_lt (cell (original ⟨i,hi⟩)).isLt
  case values =>
    intro i hi
    let c := cell (original ⟨i,hi⟩)
    have key : (l).owner mem i=c.val := owners ⟨i,hi⟩
    have full := (image.private_census N cell aux siteID edgeID portID F net codes fit original live
      frame origin desc gap c).trans_le (room c)
    have mono : PrivatePlacement.prefixCounts ((l).owner mem) desc (i+1) c.val ≤
        PrivatePlacement.prefixCounts ((l).owner mem) desc J c.val :=
      Finset.sum_le_sum_of_subset (Finset.range_mono hi)
    simp only [PrivatePlacement.prefixCounts,Finset.sum_range_succ,key,ite_true] at mono
    change mem ((l).supplied+(l).owner mem i)+gap+PrivatePlacement.prefixCounts ((l).owner mem) desc i ((l).owner mem i) < _ ∧
      PrivatePlacement.prefixCounts ((l).owner mem) desc i ((l).owner mem i)+desc < _
    rw [key]
    unfold PrivatePlacement.prefixCounts at full ⊢
    omega
  all_goals dsimp only [privateLayout,bases,PrivatePlacement.Layout.scratch,PrivatePlacement.Layout.supplied] at arr ⊢
  all_goals omega

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
