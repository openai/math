import OAI.Computability.BorderVNP.PackedFrozenBirthTape
import OAI.Computability.BorderVNP.PackedInheritedSeedPacket

/-! # Compiling the main birth records in one public frame

The same finite circuit serves every physical input and attained profile. It
computes the packet words once, emits the enable and public owner at every
frozen row, and selects the complete ordered main tape of each seed. The
scalar width is justified by the physical expanded tile bound.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.Birth

open Crossing Shortening Shortening.StaticRows Shortening.SeedIntervals Shortening.CombiningStep
open InheritedProfile BankSite BankJoint ParseBatchSort VPVNP.VerifierNetwork CellAddressCircuit CellAddressPhysical
open CellSparse
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    (first : Fin D × Bool) {S : Type} [Fintype S] {n s k u C d h w b : ℕ}
    (seed : S ↪ Fin n) {σ : Type*} [Fintype σ] (F : Fields (siteCapacity e s n) (edgeCapacity e k n) u C d h w σ)
    (counts : Frame σ (S × Option (Fin e.count) × Fin w))

/-- A uniform circuit with the actual marked main records at each newly
installed site. Its retained old sites receive the empty main birth tape. -/
theorem exists_mainFrame (hm : 0 < m) (fit : siteCapacity e s n ≤ 2^b) :
    ∃ f : Frame σ (Pins (Row e first S) (S × Output e first × Fin w) b),
      f.size ≤ Fintype.card (Row e first S)*(1+b) + (counts.size+(Views.frame F).size+6+Fintype.card S *
        ((adjustNodes e + BankCircuit.headerNodes D e.count m + PaidBox.nodeBound e + nodes e first) * (100*(w+1)^2))) ∧
      (∀ (x : σ → Bool) (r : Row e first S),
        f.eval x (.inl (r,.inl ())) = true ∧ owner (f.eval x) r = (slot e seed s r.1).val) ∧
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
          (∀ a v, (schema e first S w).atSite (f.eval x) (site (.inr ⟨a,v⟩)).val =
            (emitted e first (relativeRaw e p bin perm positive first q a edge portID) v).map marked) ∧
          (∀ v, (schema e first S w).atSite (f.eval x) (site (.inl v)).val = []) := by
  obtain ⟨packets,hsize,hword⟩ := exists_seedPackets e first hm seed F counts
  refine ⟨frame (d := b) e first seed s packets,
    (frame_size e first seed s packets).trans (Nat.add_le_add_left hsize _),?_,?_⟩
  · exact fun x r => ⟨active e first seed s packets x r,owner_value e first seed s packets fit x r⟩
  · intro P _ bits p bin perm positive q oldSite oldEdge portID G site edge cell aux x rep hist prior payload M cap room
    let raw := fun a => relativeRaw e p bin perm positive first q a edge portID
    have words := hword p bin perm positive q oldSite oldEdge portID cell aux x rep hist prior payload M cap room
    exact ⟨at_seed e first seed s packets fit x raw words,at_old e first seed s packets fit x p oldSite⟩

end Packing.Inherited.FrozenTape.Birth

end BorderVNP
end Computability
end OAI
