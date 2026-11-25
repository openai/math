import OAI.Computability.BorderVNP.PackedBankInstall
import OAI.Computability.BorderVNP.PackedCellAddressOutputs

/-! # Certified physical addresses in the installed packet program

The returned site offset and cable starts are the addresses actually read
by the private checker in the sewn pack's owning cell. The proof uses the
same shared/private or crossing/supplied selection as the concrete address
circuit.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankJoint

open Crossing Shortening Shortening.StaticRows Shortening.CombiningStep ParseBatchSort VPVNP.VerifierNetwork
open CellAddressCircuit CellAddressPhysical CellAddresses

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
variable {S : Type} [Fintype S] (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
variable (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)

private noncomputable abbrev L := (output e p bin perm positive first q).layout

variable {n s k u C d h w : ℕ} (oldSite : p.layout.Site ↪ Fin s) (oldEdge : p.layout.Edge ↪ Fin k)
variable (seed : S ↪ Fin n) (portID : P ↪ Fin u)
variable (cell : (L e p bin perm positive first q).Site → Fin C)
variable (aux : (L e p bin perm positive first q).Site → ℕ)
variable {σ : Type*} [Fintype σ] (F : Fields (siteCapacity e s n) (edgeCapacity e k n) u C d h w σ)
variable (counts : Frame σ (S × Option (Fin e.count) × Fin w))
variable (ids : Frame σ (Fin (siteCapacity e s n) × Fin w))
variable {x : σ → Bool}
variable (rep : Represents (L e p bin perm positive first q) cell aux (siteRows e p oldSite seed)
  (outputRows e p bin perm positive first q oldEdge seed) portID F x)
variable (fit : ∀ c, let N := L e p bin perm positive first q
  guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c < 2^w)

include rep fit in
/-- The geometry packet carries the absolute start of the owning site's auxiliary slab. -/
theorem installed_site_value (a : S) (v : TemplateSite e) :
    let N := L e p bin perm positive first q
    let t : N.Site := .inr ⟨a,v⟩
    value (fun j => (install e seed s k counts (CellAddressViews.frame F) ids).eval x (a,.inr ⟨v,none⟩,j)) =
      siteBase N cell (cell t) (siteRows e p oldSite seed) aux ⟨t,rfl⟩ := by
  rw [install_value]
  change value (fun j => (CellAddressViews.frame F).eval x (.inr (.inl (siteSlot e s (seed a) v)),j)) = _
  rw [siteSlot_actual e p oldSite seed]
  exact CellAddressViews.site_value _ _ _ _ _ _ F rep fit _

include rep fit in
/-- The chosen source/destination reference gives the canonical word start inside its
own cell, both for shared internal cables and for nonlocal supplied cables. -/
theorem installed_endpoint_value (a : S) (v : TemplateSite e) (r : Bases e v) (edge : TemplateEdge e)
    (src : Bool) (hr : reference e v r = some (edge,src)) :
    let N := L e p bin perm positive first q
    let z : N.Edge := .inr (.inr ⟨a,edge⟩)
    let edgeID := outputRows e p bin perm positive first q oldEdge seed
    value (fun j => (install e seed s k counts (CellAddressViews.frame F) ids).eval x (a,.inr ⟨v,some (some r)⟩,j)) =
      if src then wireBase N cell (cell (N.src z)) edgeID portID aux ⟨N.src z,rfl⟩ ⟨z,.inl rfl⟩
      else wireBase N cell (cell (N.dst z)) edgeID portID aux ⟨N.dst z,rfl⟩ ⟨z,.inr rfl⟩ := by
  rw [install_value]
  cases src
  · simp only [rawWord,hr]
    change value (fun j => (CellAddressViews.frame F).eval x (.inl (.inl (.inr (edgeSlot e k (seed a) edge))),j)) = _
    rw [edgeSlot_actual e p bin perm positive first q oldEdge seed]
    exact CellAddressViews.dest_value _ _ _ _ _ _ F rep fit _
  · simp only [rawWord,hr]
    change value (fun j => (CellAddressViews.frame F).eval x (.inl (.inl (.inl (edgeSlot e k (seed a) edge))),j)) = _
    rw [edgeSlot_actual e p bin perm positive first q oldEdge seed]
    exact CellAddressViews.source_value _ _ _ _ _ _ F rep fit _

end Packing.BankJoint

end BorderVNP
end Computability
end OAI
