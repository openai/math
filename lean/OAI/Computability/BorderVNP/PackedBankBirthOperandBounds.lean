import OAI.Computability.BorderVNP.PackedBankInheritedScalarCapacity
import OAI.Computability.BorderVNP.PackedBankHeaderCapacity
import OAI.Computability.BorderVNP.PackedBankLocationBounds
import OAI.Computability.BorderVNP.PackedInheritedProfileState

/-! # Numerical bounds for the physical operands of fresh crossing sites

The intrinsic program uses the singleton cell at its site before any later
placement. Its bank therefore contains exactly its own work and incidence
words. The expanded tile counts bound both, even for an empty cable.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedProfile

open Crossing CellSparse Shortening Shortening.CombiningStep Shortening.SeedIntervals
  Shortening.StaticRows Inherited InheritedBank CellAddresses BankSite BankJoint BankCircuit
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
    (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
private noncomputable abbrev L := (output e p bin perm positive first q).layout
local notation "G" => L e p bin perm positive first q
local notation "work" => workAt e p bin perm positive first q

/-- The genuine expanded record cap on every tile of the selected crossing. -/
abbrev BirthTileCap {T : Type*} (tile : (L e p bin perm positive first q).Site → T) (prior payload : p.layout.Site → ℕ) (M : ℕ) : Prop :=
  ∀ t, localRecords G true (Sum.elim prior (fun _ => 0))
    (Sum.elim payload (fun z => bankUses e (blocks p.layout bin perm m z.1) (q z.1).val z.2))
    (fun v => tile v = t) ≤ M

/-- A common bound on the work and incident wires in every singleton birth bank. -/
noncomputable def birthCapacity (M : ℕ) := (BankCharges.bound e+1)*M

variable {T : Type*} (tile : (L e p bin perm positive first q).Site → T) (prior payload : p.layout.Site → ℕ) (M : ℕ)
    (cap : BirthTileCap e p bin perm positive first q tile prior payload M)

include cap in
/-- Singleton bank addresses remain bounded at the exact start of a zero-width row. -/
theorem birthBank_le (v : (G).Site) :
    guessedSize G id v + siteSize G id v work + suppliedSize G id v ≤ birthCapacity e M := by
  have hw : work v ≤ BankCharges.bound e*M := by
    rcases v with v | ⟨a,z⟩
    · exact Nat.zero_le _
    · exact (Nat.le_add_left _ _).trans (BankCharges.site_le e p bin perm positive first q tile prior payload M cap a z)
  let old : (G).Site → ℕ := Sum.elim prior (fun _ => 0)
  let pay : (G).Site → ℕ := Sum.elim payload (fun z => bankUses e (blocks p.layout bin perm m z.1) (q z.1).val z.2)
  have hi : incoming G v ≤ M :=
    (Nat.le_add_left _ _).trans ((payload_incoming_le G old pay v (fun z => tile z = tile v) rfl).trans (cap (tile v)))
  have hs : siteSize G id v work = work v := by rw [siteSize_eq]; simp [testedWidth]
  rw [hs]
  change guessedSize G id v + suppliedSize G id v ≤ M at hi
  unfold birthCapacity
  rw [Nat.add_mul,Nat.one_mul]
  omega

variable (a : S) {ns ne np : ℕ} (siteID : (L e p bin perm positive first q).Site ↪ Fin ns) (edgeID : (L e p bin perm positive first q).Edge ↪ Fin ne) (portID : P ↪ Fin np)
local notation "fields" => raw e p bin perm positive first q a siteID edgeID portID

include cap in
/-- The actual origin or terminal location comes from a finite site offset, its
local zero box number, or a true incident cable at the selected end. -/
theorem birthLocation_le (z : Σ v : TemplateSite e, Location e v) : fields (.inr z) ≤ birthCapacity e M := by
  have bank := birthBank_le e p bin perm positive first q tile prior payload M cap
  rcases z with ⟨v,(_ | _ | b)⟩
  · let u : (G).Site := .inr ⟨a,v⟩
    have h := siteBase_fits G id u siteID work ⟨u,rfl⟩
    exact ((Nat.le_add_right _ _).trans h).trans ((Nat.le_add_right _ _).trans (bank u))
  · exact Nat.zero_le _
  · change (reference e v b).elim 0 _ ≤ _
    cases hr : reference e v b with
    | none => exact Nat.zero_le _
    | some z =>
      let wire : (G).Edge := .inr (.inr ⟨a,z.1⟩)
      let u := incidentSite G wire z.2
      exact (wireBase_le G id u edgeID portID work ⟨u,rfl⟩ (incidentWire G wire z.2)).trans (bank u)

include cap in
/-- All prepared origin, terminal and paid operand words fit a single linear
bound from the true tile cap, including the selected counts and physical bases. -/
theorem birthPrepared_le (hm : 0 < m) (r : Prepared e) : word e fields r ≤ birthCapacity e M := by
  obtain ⟨hh,hp⟩ := BankCharges.header_le_of_tile_cap e p bin perm positive first q hm tile prior payload M cap a
  have h : BankCharges.bound e*M ≤ birthCapacity e M := by unfold birthCapacity; rw [Nat.add_mul]; omega
  rcases r with r | ⟨i,v,b⟩ | z
  · exact (hh r).trans h
  · exact (hp i v b).trans h
  · exact birthLocation_le e p bin perm positive first q tile prior payload M cap a siteID edgeID portID z

end Packing.InheritedProfile

end BorderVNP
end Computability
end OAI
