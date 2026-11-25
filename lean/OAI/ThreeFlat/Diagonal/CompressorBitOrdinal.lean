import OAI.ThreeFlat.Diagonal.CompressorDemandFinite
import OAI.ThreeFlat.Diagonal.CompressorDemandOrdinal

namespace OAI
/-! # Physical TT prefix lengths for the AB endpoint reader -/
namespace ThreeFlat.Diagonal.CompressorPacking
open Computability.VPVNP.Compression Computability.BorderVNP.Packing.CellSlabs
open scoped Classical BigOperators
variable {V H Tag L : Type*} {c d T R : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable (P : PackingData V H Tag L d c)
variable (v : V ↪ ℕ) (tag : Tag ↪ Fin T) (lane : L ↪ Fin R)
local notation "absId" => demandOrdinal P v tag lane

def lowIndex (z : BitWord c × H) : ℕ := (Native.tagOrdinal c z.1).val + 2^c*(P.slotLabel z.2).val

omit [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L] [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] in
theorem ordinal_bundle_lt (p : Site V Tag L × Fin d) (a b : BitWord c × H) :
    absId (p,a) < absId (p,b) ↔ lowIndex P a < lowIndex P b := by
  simp only [demandOrdinal_formula,lowIndex,Nat.mul_add]
  omega

/-- In the `h,u` loop the old bit sits after exactly those positive-width
TT intervals whose little-endian pair index is smaller. -/
theorem oldBit_position (width : Arc V H Tag L d c → ℕ) (p : Site V Tag L × Fin d)
    (a : ThickAt P p) (k : Fin (width a.val)) :
    (oldBit P absId width p ⟨a,k⟩).val =
      (∑ h : Fin d, ∑ u : Fin (2^c),
        if u.val+2^c*h.val < lowIndex P a.val.2 then gatherElements P width p h u else 0) + k.val := by
  let earlier (e : Arc V H Tag L d c) := if absId e < absId a.val then width e else 0
  change thickWidth P earlier p + k.val = _
  rw [←gather_elements P earlier p]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro u _
  let z := ((Native.tagOrdinal c).symm u,P.slotLabel.symm h)
  have aa : (p,a.val.2) = a.val := Prod.ext a.property.1.symm rfl
  have ord : absId (p,z)<absId a.val ↔ u.val+2^c*h.val < lowIndex P a.val.2 := by
    rw [←aa,ordinal_bundle_lt]
    simp [lowIndex,z]
  by_cases hit : ttAt P p z <;> by_cases before : u.val+2^c*h.val < lowIndex P a.val.2 <;>
    simp only [gatherElements,earlier,←ord,show ((Native.tagOrdinal c).symm u,P.slotLabel.symm h)=z from rfl,
      hit,ite_true,ite_false] <;> simp_all

end ThreeFlat.Diagonal.CompressorPacking

end OAI
