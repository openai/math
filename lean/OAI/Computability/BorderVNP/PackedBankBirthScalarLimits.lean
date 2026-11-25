import OAI.Computability.BorderVNP.PackedBankBirthOperandBounds
import OAI.Computability.BorderVNP.PackedBankInheritedScalarBounds
import OAI.Computability.BorderVNP.CellPacketFieldMonotone

/-! # A numerical scalar bound uniform over fresh crossing-site templates -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing CellSparse Shortening Shortening.CombiningStep Shortening.SeedIntervals Shortening.StaticRows
  InheritedProfile BankSite BankJoint BankCharges BankPacket
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- Fixed maximum arithmetic coefficient of the frozen record tape, over every
first spoke and every physical site of the paid identity. -/
noncomputable def birthWordCoefficient :=
  Finset.univ.sup fun t : Fin D × Bool => Finset.univ.sup fun v : TemplateSite e => wordCoefficient e t v

/-- The two data-dependent arguments are the expanded tile load and the old
bin population. The latter covers the untrimmed ordinals of empty hook rows. -/
noncomputable def birthScalarLimit (M B : ℕ) :=
  3 + birthWordCoefficient e*(birthCapacity e M+1) + 2*birthCapacity e M + 2*B + 1

/-- All fixed-record fields are controlled by the same template constant. -/
theorem birthFrozen_le (t : Fin D × Bool) (v : TemplateSite e) (M B : ℕ) :
    wordCoefficient e t v * (birthCapacity e M+1) ≤ birthScalarLimit e M B := by
  have h : wordCoefficient e t v ≤ birthWordCoefficient e :=
    (Finset.le_sup (f := fun u : TemplateSite e => wordCoefficient e t u) (Finset.mem_univ v)).trans
      (Finset.le_sup (f := fun a : Fin D × Bool => Finset.univ.sup fun u : TemplateSite e => wordCoefficient e a u)
        (Finset.mem_univ t))
  have hc := Nat.mul_le_mul_right (birthCapacity e M+1) h
  unfold birthScalarLimit
  omega

/-- Numeric raw record bounds cover the marked integer tape, including the
fixed opcode of a profile command. -/
theorem birthScalar_of_records (M B : ℕ) (s : Site)
    (h : ∀ r ∈ s.rows, Packet.RecordFields r (birthScalarLimit e M B)) :
    s.ScalarBound (birthScalarLimit e M B) := by
  intro x hx
  apply (s.scalarBound_of_recordFields h x hx).trans
  unfold birthScalarLimit
  omega

variable [NeZero D] {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
    (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
    {T : Type*} (tile : (output e p bin perm positive first q).layout.Site → T) (prior payload : p.layout.Site → ℕ)
    (M : ℕ) (cap : BirthTileCap e p bin perm positive first q tile prior payload M) (hm : 0 < m)
    (a : S) {ns ne np : ℕ} (siteID : (output e p bin perm positive first q).layout.Site ↪ Fin ns)
    (edgeID : (output e p bin perm positive first q).layout.Edge ↪ Fin ne) (portID : P ↪ Fin np)
local notation3 "raw₀" => InheritedProfile.raw e p bin perm positive first q a siteID edgeID portID

include cap hm in
/-- Every public field of the actual origin at birth fits the common scalar
bound, before placement and regardless of the size of a zero-width selector. -/
theorem origin_scalarBound (B : ℕ) :
    (originSite e p bin perm positive first q a siteID edgeID portID).ScalarBound (birthScalarLimit e M B) := by
  apply birthScalar_of_records
  intro r hr
  simp only [originSite,Site.rows,List.reverse_singleton,List.flatten_cons,List.flatten_nil,List.append_nil] at hr
  change r ∈ (format e first (.inl ())).2.map (RecordCode.read (originWords e raw₀)) at hr
  exact (emitted_recordFields e first (.inl ()) (originWords e raw₀) (birthCapacity e M)
    (fun i => birthPrepared_le e p bin perm positive first q tile prior payload M cap a siteID edgeID portID
      hm (pin e (.inl ()) i)) r hr).mono (birthFrozen_le e first (.inl ()) M B)

end Packing.Inherited

end BorderVNP
end Computability
end OAI
