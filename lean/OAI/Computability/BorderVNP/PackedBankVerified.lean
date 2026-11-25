import OAI.Computability.BorderVNP.PackedBankLocationBounds

/-! # Verified physical seed-bank packet stage

The Boolean circuit is chosen before the current pack, the input bits, the
histogram branch, or the local table contents. Every represented branch of
the real combining step produces the expected tagged words under a common
tile bound. All address arithmetic is discharged by a single binary-width
inequality.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankJoint

open Crossing Shortening Shortening.StaticRows Shortening.CombiningStep Shortening.SeedIntervals
open CellAddressCircuit CellAddressPhysical CellAddresses ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m) (first : Fin D × Bool)

/-- One explicit binary width covering both table-addressing and expression evaluation. -/
noncomputable def packetWidth (M U : ℕ) : ℕ :=
  Nat.clog 2 (addressCoefficient e first * (max (BankCharges.bound e * M) U + 1) + 1)

/-- The chosen width includes the carry bit even at exact powers of two. -/
theorem packetWidth_room (M U : ℕ) :
    addressCoefficient e first * (max (BankCharges.bound e * M) U + 1) < 2^(packetWidth e first M U) :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_pow_clog (by decide : 1 < 2) _)

/-- The same program verifies all physical inputs, emitting the exact flat records at
every origin, terminal, and repeated paid-table site. A cell layout includes only
the represented internal wires, supplied ports, and actual staged site slots.
The box lists may contain private one-copy tables. Only their counts enter the
public prefix scan. -/
theorem physical_pipeline [NeZero D] (hm : 0 < m) {S : Type} [Fintype S]
    {n s k u C d h w : ℕ} (seed : S ↪ Fin n) {τ σ : Type*} [Fintype τ] [Fintype σ]
    (F : Fields (siteCapacity e s n) (edgeCapacity e k n) u C d h w τ)
    (boxCount : Fin (siteCapacity e s n) → Fin w → τ) (countPin : S × Option (Fin e.count) × Fin w → τ)
    (prior : Frame σ τ) (valid : τ) :
    ∃ f : Frame σ ((S × Output e first × Fin w) ⊕ Unit),
      f.size ≤ prior.size + (CellAddressViews.frame F).size +
        (2+2*(siteCapacity e s n+1)*BankBoxOrdinal.laneCost (Nat.clog 2 (siteCapacity e s n)) h w) +
        4 + Fintype.card S * ((BankCircuit.headerNodes D e.count m + PaidBox.nodeBound e + nodes e first) * (100*(w+1)^2)) ∧
      (∀ x, f.eval x (.inr ()) = prior.eval x valid) ∧
      ∀ {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
        (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S) (positive : p.layout.Edge → Bool)
        (q : Counts e p bin perm) (oldSite : p.layout.Site ↪ Fin s) (oldEdge : p.layout.Edge ↪ Fin k)
        (portID : P ↪ Fin u) (x : σ → Bool),
        let L := (output e p bin perm positive first q).layout
        let publicBits := prior.eval x
        ∀ (cell : L.Site → Fin C) (aux : L.Site → ℕ) (oldHist oldPayload : p.layout.Site → ℕ)
          (M U : ℕ) {α : Type*} (boxes : Fin (siteCapacity e s n) → List α),
          Represents L cell aux (siteRows e p oldSite seed) (outputRows e p bin perm positive first q oldEdge seed)
            portID F publicBits →
          (∀ a i, value (fun j => publicBits (countPin (a,i,j))) = i.elim (blocks p.layout bin perm m a) (q a).val) →
          (∀ v, value (publicBits ∘ boxCount v) = (boxes v).length) →
          (∀ c, (BankBoxOrdinal.table (fun v => value (publicBits ∘ F.owner v)) boxes c).length ≤ U) →
          (∀ c, guessedSize L cell c + siteSize L cell c aux + suppliedSize L cell c ≤ U) →
          (∀ c, localRecords L true (Sum.elim oldHist (fun _ => 0))
            (Sum.elim oldPayload (fun z => bankUses e (blocks p.layout bin perm m z.1) (q z.1).val z.2))
            (fun v => cell v = c) ≤ M) →
          addressCoefficient e first * (max (BankCharges.bound e * M) U + 1) < 2^w →
          ∀ a (z : Output e first),
            value (fun j => f.eval x (.inl (a,z,j))) =
              (CellSparse.Packet.fieldList CellSparse.Packet.record (emitted e first
                (directoryRaw e seed s k F boxCount countPin publicBits a) z.1))[z.2.val]?.getD 0 := by
  obtain ⟨f,hsize,hvalid,hwords⟩ := pipeline e seed s k F boxCount countPin first prior valid
  refine ⟨f,hsize,hvalid,?_⟩
  intro P _ bits p bin perm positive q oldSite oldEdge portID x L publicBits cell aux oldHist oldPayload
    M U α boxes hrep hcount hbox htotal hcell hcap hroom a z
  let raw := directoryRaw e seed s k F boxCount countPin publicBits a
  have hpos : 0 < addressCoefficient e first := by unfold addressCoefficient; omega
  have hU : U < 2^w := (le_max_right (BankCharges.bound e*M) U).trans_lt
    ((Nat.lt_succ_self _).trans_le (Nat.le_mul_of_pos_left _ hpos) |>.trans hroom)
  have hboxsum c : (∑ v, if value (publicBits ∘ F.owner v) = c then value (publicBits ∘ boxCount v) else 0) ≤ U := by
    simpa only [hbox,BankBoxOrdinal.table_length] using htotal c
  have hloc := raw_location_le e p bin perm positive first q oldSite oldEdge seed portID cell aux F boxCount countPin
    hrep U hU hcell hboxsum a
  have counts (i : Option (Fin e.count)) : raw (.inl i) = i.elim (blocks p.layout bin perm m a) (q a).val := by
    simpa [raw,directoryRaw,rawWord] using hcount a i
  obtain ⟨hf,hz⟩ := fits_physical e first p bin perm positive q hm cell oldHist oldPayload M hcap a raw counts hloc hroom
  exact hwords x a hf z (hz z)

end Packing.BankJoint

end BorderVNP
end Computability
end OAI
