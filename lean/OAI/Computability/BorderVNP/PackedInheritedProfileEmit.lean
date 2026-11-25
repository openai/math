import OAI.Computability.BorderVNP.PackedInheritedHookBlock

/-! # Immutable profile-site blocks emitted by the intrinsic packet compiler

All static prefix rows are read from the shared relative raw operand frame.
At a terminal the dynamic hook payload follows the fixed prefix in old-cable
order. Together these are exactly the profile-site state's retained records.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedProfile

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Inherited InheritedHook BankSite BankJoint BankPacket CellSparse DirectoryCircuit
open ParseBatchSort VPVNP.VerifierNetwork CellAddressCircuit CellAddressPhysical
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {P S : Type} [Fintype P] [Fintype S] {bits : P → ℕ} (p : Pack D P bits K)
variable (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
variable (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
private noncomputable abbrev G := (output e p bin perm positive first q).layout
variable (a : S) {ns ne np : ℕ} (siteID : (G e p bin perm positive first q).Site ↪ Fin ns)
variable (edgeID : (G e p bin perm positive first q).Edge ↪ Fin ne) (portID : P ↪ Fin np)
local notation3 "rel" => relativeRaw e p bin perm positive first q a edgeID portID
local notation3 "raw₀" => raw e p bin perm positive first q a siteID edgeID portID

/-- Every profile-prefix row is emitted with the same actual operands as in
the accepted intrinsic state. -/
theorem relative_profile_emitted (r : Unit ⊕ (Fin D × Bool)) :
    emitted e first rel (profileNode e r) = emitted e first raw₀ (profileNode e r) := by
  have h := funext (relative_profile_words e p bin perm positive first q a edgeID portID siteID r)
  exact congrArg (fun x => (BankJoint.rows e first (profileNode e r)).map (RecordCode.read x)) h

/-- All immutable origin rows come from the common native birth encoder. -/
theorem origin_emitted :
    emitted e first rel (.inl ()) = (originSite e p bin perm positive first q a siteID edgeID portID).rows := by
  have he := relative_profile_emitted e p bin perm positive first q a siteID edgeID portID (.inl ())
  change emitted e first rel (.inl ()) = emitted e first raw₀ (.inl ()) at he
  rw [he]
  simp [originSite,Site.rows]

/-- The retained terminal state contains the relative-operand prefix followed by
the complete physical hook block, in that order. -/
theorem terminal_emitted (names : S → ℕ) (t : Fin D × Bool) :
    emitted e first rel (.inr (.inl t)) ++ hookRows e p bin perm positive first q a siteID edgeID portID names t =
      (terminalSite e p bin perm positive first q a siteID edgeID portID names t).rows := by
  have he := relative_profile_emitted e p bin perm positive first q a siteID edgeID portID (.inr t)
  change emitted e first rel (.inr (.inl t)) = emitted e first raw₀ (.inr (.inl t)) at he
  rw [he]
  simp [terminalSite,Site.rows]

end Packing.InheritedProfile

end BorderVNP
end Computability
end OAI
