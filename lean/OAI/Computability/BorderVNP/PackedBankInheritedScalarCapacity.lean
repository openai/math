import OAI.Computability.BorderVNP.PackedBankInheritedSiteCharges
import OAI.Computability.BorderVNP.ShortenEpochRoundRecords

/-! # Scalar capacities of retained site banks

The private payload and the current incoming words at a site occupy separate
parts of its expanded record count. After sewing, that payload includes the
previous incoming words as well as the previous private bank. The resulting
regional bound covers the full address range of a retained interval tie.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedBank

open Crossing Shortening Epoch
open private localRecords_mono from OAI.Computability.BorderVNP.ShortenEpochRoundRecords

variable {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)

/-- A region containing a site counts at least its mandatory box descriptor. -/
theorem one_le_region (ex : Bool) (prior payload : N.Site → ℕ) (v : N.Site)
    (test : N.Site → Prop) (hv : test v) : 1 ≤ localRecords N ex prior payload test :=
  (one_le_siteRecords N ex prior payload v).trans
    (localRecords_mono N ex prior payload (fun _ h => h ▸ hv))

/-- Expanded regional records pay for the private payload and the distinct incoming words together. -/
theorem payload_incoming_le (prior payload : N.Site → ℕ) (v : N.Site)
    (test : N.Site → Prop) (hv : test v) :
    payload v + Inherited.incoming N v ≤ localRecords N true prior payload test := by
  let zero := fun _ : N.Site => 0
  have wires : Inherited.incoming N v ≤ localRecords N true zero zero (fun u => u = v) :=
    CellAddresses.wireCapacity_le N id v zero zero
  have boxes := exchange_site_records N true zero zero prior payload v
  change localRecords N true prior payload (fun u => u = v) + 1 =
    localRecords N true zero zero (fun u => u = v) + (prior v + (1 + payload v)) at boxes
  apply le_trans _ (localRecords_mono N true prior payload (s := fun u => u = v) (fun _ h => h ▸ hv))
  omega

end Packing.InheritedBank

namespace Packing.Inherited

open Crossing Shortening Shortening.CombiningStep InheritedBank

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {P : Type*} [Fintype P] {bits : P → ℕ}
    (e : PaidIdentity K D m) (p : Pack D P bits K) {A : Type} [Fintype A]
    (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)

private noncomputable abbrev G := (output e p bin perm positive first q).layout

/-- The scalar extent used by a retained tie fits in any tested region containing its old site. -/
theorem retained_extent_le (old : p.layout.Site) (s : Site) (prior payload : p.layout.Site → ℕ)
    (hin : s.incoming = incoming p.layout old) (hwork : s.work ≤ payload old)
    (test : (G e p bin perm positive first q).Site → Prop) (hmem : test (.inl old)) :
    max 1 (s.size + incoming (G e p bin perm positive first q) (.inl old)) ≤
      localRecords (G e p bin perm positive first q) true (nextPrior e p bin perm positive first q prior)
        (nextPayload e p bin perm positive first q payload) test := by
  let L := G e p bin perm positive first q
  let hist := nextPrior e p bin perm positive first q prior
  let pay := nextPayload e p bin perm positive first q payload
  apply max_le (one_le_region L true hist pay (.inl old) test hmem)
  apply le_trans _ (payload_incoming_le L hist pay (.inl old) test hmem)
  apply Nat.add_le_add_right
  rw [Site.size, hin, incoming_eq_widths p.layout old]
  exact Nat.add_le_add_right hwork _

end Packing.Inherited

end BorderVNP
end Computability
end OAI
