import OAI.Computability.BorderVNP.PackedInheritedSeedCapacity
import OAI.Computability.BorderVNP.PackedInheritedBirthRawFrame
import OAI.Computability.BorderVNP.PackedBankVerified

/-! # Compiled immutable seed packets with physical resource bounds

The public finite gate list first computes intrinsic addresses from the real
pointer and width registers. It then serializes the origin, terminal and paid
records. Every intermediate arithmetic fit follows from the common tile cap
and one binary word-width bound chosen before the geometry and histogram.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedProfile

open Crossing Shortening Shortening.StaticRows Shortening.SeedIntervals Shortening.CombiningStep
open Inherited BankSite BankJoint ParseBatchSort VPVNP.VerifierNetwork CellAddressCircuit CellAddressPhysical
open CellSparse
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    (first : Fin D × Bool) (hm : 0 < m) {S : Type} [Fintype S] {n s k u C d h w : ℕ}
    (seed : S ↪ Fin n) {σ : Type*} [Fintype σ] (F : Fields (siteCapacity e s n) (edgeCapacity e k n) u C d h w σ)
    (counts : Frame σ (S × Option (Fin e.count) × Fin w))

include hm in
/-- A single bounded gate list emits every intrinsic seed packet, using the
real histogram and cell pointer/width columns on every admissible input. -/
theorem exists_seedPackets :
    ∃ f : Frame σ (S × Output e first × Fin w),
      f.size ≤ counts.size+(Views.frame F).size+6+Fintype.card S *
        ((adjustNodes e + BankCircuit.headerNodes D e.count m + PaidBox.nodeBound e + nodes e first) * (100*(w+1)^2)) ∧
      ∀ {P : Type} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K) (bin : p.layout.Edge → Option S)
        (perm : Fin D → Equiv.Perm S) (positive : p.layout.Edge → Bool) (q : Counts e p bin perm)
        (oldSite : p.layout.Site ↪ Fin s) (oldEdge : p.layout.Edge ↪ Fin k) (portID : P ↪ Fin u),
        let G := (output e p bin perm positive first q).layout
        let site := siteRows e p oldSite seed
        let edge := outputRows e p bin perm positive first q oldEdge seed
        ∀ (cell : G.Site → Fin C) (aux : G.Site → ℕ) (x : σ → Bool), Represents G cell aux site edge portID F x →
          (∀ a i, value (fun j => counts.eval x (a,i,j)) = i.elim (blocks p.layout bin perm m a) (q a).val) →
          ∀ (prior payload : p.layout.Site → ℕ) (M : ℕ),
          (∀ c, localRecords G true (Sum.elim prior (fun _ => 0))
            (Sum.elim payload (fun z => bankUses e (blocks p.layout bin perm m z.1) (q z.1).val z.2))
            (fun v => cell v = c) ≤ M) →
          addressCoefficient e first * (BankCharges.bound e * M + M + 1) < 2^w →
          ∀ a (z : Output e first),
            value (fun j => f.eval x (a,z,j)) =
              (Packet.fieldList Packet.record (emitted e first (relativeRaw e p bin perm positive first q a edge portID) z.1))[z.2.val]?.getD 0 := by
  obtain ⟨source,hs,he⟩ := exists_relativeRawFrame e seed F counts
  obtain ⟨f,hf,run⟩ := exists_packetFrame e first w source
  refine ⟨f,?_,?_⟩
  · simp only [Nat.add_mul,Nat.mul_add] at hf ⊢
    omega
  · intro P _ bits p bin perm positive q oldSite oldEdge portID G site edge cell aux x rep hcount prior payload M cap room a z
    let U := BankCharges.bound e*M+M
    have hpos : 0 < addressCoefficient e first := by unfold addressCoefficient; omega
    have hU : U < 2^w := (Nat.lt_succ_self U).trans_le (Nat.le_mul_of_pos_left _ hpos) |>.trans room
    have hi : ∀ v, incoming G v < 2^w := fun v =>
      (incoming_le_cap e p bin perm positive first q cell prior payload M cap v).trans_lt ((Nat.le_add_left _ _).trans_lt hU)
    have hv := he p bin perm positive first q oldSite oldEdge portID cell aux x rep hi a (hcount a)
      (fun v => (seed_slab_le e p bin perm positive first q cell prior payload M cap a v).trans_lt hU)
    let raw := relativeRaw e p bin perm positive first q a edge portID
    have wordRoom : addressCoefficient e first * (max (BankCharges.bound e*M) U+1) < 2^w := by
      rwa [max_eq_right (Nat.le_add_right _ _)]
    obtain ⟨hfit,words⟩ := fits_physical e first p bin perm positive q hm cell prior payload M cap a raw (fun _ => rfl)
      (relative_location_le e p bin perm positive first q cell prior payload M cap edge portID a) wordRoom
    have h := run x a
    dsimp only at h
    rw [funext hv] at h
    exact h hfit z (words z)

end Packing.InheritedProfile

end BorderVNP
end Computability
end OAI
