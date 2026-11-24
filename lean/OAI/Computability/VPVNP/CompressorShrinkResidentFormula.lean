import OAI.Computability.VPVNP.CompressorRecordsDemandOutput
import OAI.Computability.VPVNP.CompressorRecordsShrinkHistory

/-!
# Reading resident owners in the selected shrinking layout

A dense resident ordinal consists of a motif number followed by a four-way
absorbed-edge digit or a six-way map-party digit. Its owner word is the
corresponding role in the four-word row of the absolute CD arc.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkResidentFormula

open Compression Compression.SurvivingSlots BurstRAM PairSimulation.LocalHistory ShrinkHistoryRows

variable {a g w : ℕ} (X : State a (packingLaneBits a g))

private theorem productOrdinal {n : ℕ} (m : X.packingData.Motif) (t : Fin n) :
    (((shrinkMotifOrder X).prod (Order.fin n)).entries.symm (m,t)).val =
      (ShrinkMotifOrder.stateNumber X m).val * n + t.val := by
  change t.val + n * (ShrinkMotifOrder.stateNumber X m).val = _
  ac_rfl

theorem hiddenOrdinal (m : X.packingData.Motif) (t : Fin 4) :
    ((hiddenOrder X).entries.symm (m,t)).val = (ShrinkMotifOrder.stateNumber X m).val * 4 + t.val :=
  productOrdinal X m t

theorem mapOrdinal (m : X.packingData.Motif) (t : Fin 6) :
    ((mapOrder X).entries.symm (m,t)).val = (ShrinkMotifOrder.stateNumber X m).val * 6 + t.val :=
  productOrdinal X m t

private theorem digits_of_eq {j m n t : ℕ} (ht : t < n) (eq : j = m*n + t) :
    j/n = m ∧ j%n = t := by
  subst j
  constructor
  · rw [Nat.mul_comm, Nat.mul_add_div (Nat.zero_le t |>.trans_lt ht), Nat.div_eq_of_lt ht, Nat.add_zero]
  · exact Nat.mul_add_mod_of_lt ht

private theorem digits_at {M : Type*} {size n : ℕ} (order : Fin size ≃ M × Fin n) (number : M → ℕ)
    (ordinal : ∀ (m : M) (t : Fin n), (order.symm (m,t)).val = number m*n + t.val) (j : Fin size) :
    j.val/n = number (order j).1 ∧ j.val%n = (order j).2.val :=
  digits_of_eq (order j).2.isLt ((congrArg Fin.val (order.symm_apply_apply j)).symm.trans
    (ordinal (order j).1 (order j).2))

set_option maxHeartbeats 1500000 in
theorem hiddenDigits (j : Fin (hiddenOrder X).length) :
    j.val / 4 = (ShrinkMotifOrder.stateNumber X ((hiddenOrder X).entries j).1).val ∧
    j.val % 4 = ((hiddenOrder X).entries j).2.val :=
  digits_at (hiddenOrder X).entries (fun m => (ShrinkMotifOrder.stateNumber X m).val) (hiddenOrdinal X) j

set_option maxHeartbeats 1500000 in
theorem mapDigits (j : Fin (mapOrder X).length) :
    j.val / 6 = (ShrinkMotifOrder.stateNumber X ((mapOrder X).entries j).1).val ∧
    j.val % 6 = ((mapOrder X).entries j).2.val :=
  digits_at (mapOrder X).entries (fun m => (ShrinkMotifOrder.stateNumber X m).val) (mapOrdinal X) j

variable {layout : Bool} {base : ℕ} {mem : Memory w}

private theorem readback_at {n : ℕ} (role : Fin n → PackedRole)
    (roles : DemandRAM.RoleColumns X layout base mem)
    (oldFit : ((shrinkMotifOrder X).prod (Order.fin n)).length ≤ 2^w)
    (newFit : (packedOrder X).length ≤ 2^w)
    (j : Fin ((shrinkMotifOrder X).prod (Order.fin n)).length) :
    let old := (shrinkMotifOrder X).prod (Order.fin n)
    let p := old.entries j
    mem (base + 4 * (DemandRAM.absoluteIndex X p.1.val).val + SlotOwners.roleOffset (role p.2)) =
      encodedPlacement old.entries.symm (packedOrder X).entries.symm
        (fun x => packedSiteEquiv (X.packingData.survivingRole layout (role x.2) x.1)) (Fin.ofNat _ j.val) := by
  let old := (shrinkMotifOrder X).prod (Order.fin n)
  apply Fin.ext
  rw [encodedPlacement_eq _ _ _ oldFit newFit j]
  exact roles.packed (old.entries j).1 (role (old.entries j).2)

theorem hidden_readback_at (roles : DemandRAM.RoleColumns X layout base mem)
    (oldFit : (hiddenOrder X).length ≤ 2^w) (newFit : (packedOrder X).length ≤ 2^w)
    (j : Fin (hiddenOrder X).length) :
    let p := (hiddenOrder X).entries j
    mem (base + 4 * (DemandRAM.absoluteIndex X p.1.val).val +
      SlotOwners.roleOffset (ShrinkMotif.internalRole layout p.2)) =
      encodedPlacement (hiddenOrder X).entries.symm (packedOrder X).entries.symm
        (X.packingData.shrinkInternalOwner layout) (Fin.ofNat _ j.val) :=
  readback_at X (ShrinkMotif.internalRole layout) roles oldFit newFit j

theorem map_readback_at (roles : DemandRAM.RoleColumns X layout base mem)
    (oldFit : (mapOrder X).length ≤ 2^w) (newFit : (packedOrder X).length ≤ 2^w)
    (j : Fin (mapOrder X).length) :
    let p := (mapOrder X).entries j
    mem (base + 4 * (DemandRAM.absoluteIndex X p.1.val).val +
      SlotOwners.roleOffset (ShrinkMotif.partyRole layout p.2)) =
      encodedPlacement (mapOrder X).entries.symm (packedOrder X).entries.symm
        (fun x => X.packingData.shrinkPartySite layout x.1 x.2) (Fin.ofNat _ j.val) :=
  readback_at X (ShrinkMotif.partyRole layout) roles oldFit newFit j

theorem hidden_readback (roles : DemandRAM.RoleColumns X layout base mem)
    (oldFit : (hiddenOrder X).length ≤ 2^w) (newFit : (packedOrder X).length ≤ 2^w)
    (m : X.packingData.Motif) (t : Fin 4) :
    (mem (base + 4 * (DemandRAM.absoluteIndex X m.val).val +
      SlotOwners.roleOffset (ShrinkMotif.internalRole layout t))).val =
      (encodedPlacement (w := w) (hiddenOrder X).entries.symm (packedOrder X).entries.symm
        (X.packingData.shrinkInternalOwner layout)
        (Fin.ofNat _ ((ShrinkMotifOrder.stateNumber X m).val * 4 + t.val))).val := by
  have h := hidden_readback_at X roles oldFit newFit ((hiddenOrder X).entries.symm (m,t))
  simpa only [Equiv.apply_symm_apply,hiddenOrdinal] using congrArg Fin.val h

theorem map_readback (roles : DemandRAM.RoleColumns X layout base mem)
    (oldFit : (mapOrder X).length ≤ 2^w) (newFit : (packedOrder X).length ≤ 2^w)
    (m : X.packingData.Motif) (t : Fin 6) :
    (mem (base + 4 * (DemandRAM.absoluteIndex X m.val).val +
      SlotOwners.roleOffset (ShrinkMotif.partyRole layout t))).val =
      (encodedPlacement (w := w) (mapOrder X).entries.symm (packedOrder X).entries.symm
        (fun x => X.packingData.shrinkPartySite layout x.1 x.2)
        (Fin.ofNat _ ((ShrinkMotifOrder.stateNumber X m).val * 6 + t.val))).val := by
  have h := map_readback_at X roles oldFit newFit ((mapOrder X).entries.symm (m,t))
  simpa only [Equiv.apply_symm_apply,mapOrdinal] using congrArg Fin.val h

end CompressorRecords.ShrinkResidentFormula

end VPVNP
end Computability
end OAI
