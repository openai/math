import OAI.Computability.BorderVNP.PackedBankBirthScalarLimits
import OAI.Computability.BorderVNP.PackedInheritedPaidModel

/-! # Actual operands of a repeated paid site at birth

Its full repeated bundle occupies two consecutive work areas. An incoming
bundle's intrinsic start may coincide with the end of its bank at width zero.
Both cases obey the same scalar cap as the origin and terminal profiles.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing CellSparse Shortening Shortening.CombiningStep Shortening.SeedIntervals Shortening.StaticRows
  InheritedProfile InheritedBank BankCharges BankPacket
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
    (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
    {T : Type*} (tile : (output e p bin perm positive first q).layout.Site → T) (prior payload : p.layout.Site → ℕ)
    (M : ℕ) (cap : BirthTileCap e p bin perm positive first q tile prior payload M) (hm : 0 < m)
    (a : S) (i : Fin e.count) (v : (e.net i).Site) {ne np : ℕ}
    (edgeID : (output e p bin perm positive first q).layout.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (position : e.Entry → ℕ)
local notation3 "G" => (output e p bin perm positive first q).layout
local notation3 "ws" => PaidBox.widths (e.net i) v
local notation3 "c₀" => (q a).val i
local notation3 "start₀" => PaidSite.starts e p bin perm positive first q a i v edgeID portID
local notation3 "site₀" => PaidPhysical.site e p bin perm positive first q a i v
local notation3 "V₀" => (Sum.inr (Sum.inr ⟨i,v⟩) : TemplateSite e)

include cap hm in
/-- The physical source, affine copy headers and zero local box number of
every stored paid row fit the common numerical cap. This includes a paid
site of multiplicity zero, whose private table is still stored once. -/
theorem paid_scalarBound (B : ℕ) :
    (PaidSite.physical e p bin perm positive first q a i v edgeID portID position).ScalarBound
      (birthScalarLimit e M B) := by
  let S₀ := birthCapacity e M
  let C := BankCharges.bound e*M
  let data := PaidSite.source ws c₀ start₀
  let x := PaidBinding.fields ws c₀ 0 0 data
  have hb : C ≤ S₀ := by dsimp [C,S₀,birthCapacity]; rw [Nat.add_mul]; omega
  have hinc : incoming G site₀ ≤ M :=
    (Nat.le_add_left _ _).trans ((payload_incoming_le G (Sum.elim prior (fun _ => 0))
      (Sum.elim payload (fun z => bankUses e (blocks p.layout bin perm m z.1) (q z.1).val z.2)) site₀
      (fun z => tile z = tile site₀) rfl).trans (cap (tile site₀)))
  have hwork : PaidSite.work ws c₀ ≤ C := by
    have hs := site_le e p bin perm positive first q tile prior payload M cap a V₀
    change _ + c₀*(1+2*PaidBox.arity e i v) ≤ C at hs
    change c₀*PaidBox.arity e i v + c₀*PaidBox.arity e i v ≤ C
    rw [Nat.mul_add,Nat.mul_one,Nat.mul_left_comm _ 2] at hs
    omega
  have room := PaidSite.physical_room e p bin perm positive first q a i v edgeID portID
  obtain ⟨_,hh⟩ := header_le_of_tile_cap e p bin perm positive first q hm tile prior payload M cap a
  have hx : ∀ b, x b ≤ S₀ := by
    rintro (_ | _ | h | r)
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact (hh i v h).trans hb
    · have start : start₀ r ≤ M := ((Nat.le_add_right _ _).trans (room r)).trans hinc
      change PaidSite.work ws c₀ + start₀ r ≤ S₀
      exact (Nat.add_le_add hwork start).trans_eq (by dsimp [C,S₀,birthCapacity]; rw [Nat.add_mul,Nat.one_mul])
  apply birthScalar_of_records
  intro r hr
  change r ∈ (PaidSite.born ws c₀ (incoming G site₀) start₀ (PaidBox.tableFactor e position i v)).directory.records at hr
  rw [PaidSite.directory] at hr
  change r ∈ (format e first V₀).2.map (RecordCode.read x) at hr
  exact (emitted_recordFields e first V₀ x S₀ hx r hr).mono (birthFrozen_le e first V₀ M B)

end Packing.Inherited

end BorderVNP
end Computability
end OAI
