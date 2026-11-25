import OAI.Computability.BorderVNP.PackedBankPipeline

/-! # Bounds on every installed physical address

A local wire start never exceeds the cell's complete canonical, auxiliary
and supplied slab length, including zero-width wires. A merged box prefix
never exceeds the total number of box entries in that cell. These bounds
apply to every location pin consumed by the public packet program.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankJoint

open Crossing Shortening Shortening.StaticRows Shortening.CombiningStep ParseBatchSort VPVNP.VerifierNetwork
open CellAddressCircuit CellAddressPhysical CellAddresses
open scoped Classical

private theorem start_le {A : Type*} [Fintype A] (row : A ↪ ℕ) (width : A → ℕ) (a : A) :
    CellSlabs.start row width a ≤ ∑ t, width t :=
  (Nat.le_add_right _ _).trans (CellSlabs.end_le_capacity row width a)

/-- Upper bound on a site's local start of a physical cable, even when the cable is empty. -/
theorem wireBase_le {D k p : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    {C : Type} (cell : N.Site → C) (c : C) (edgeID : N.Edge ↪ Fin k) (portID : P ↪ Fin p)
    (aux : N.Site → ℕ) (v : {v : N.Site // cell v = c})
    (z : {z : N.Edge // N.src z = v.val ∨ N.dst z = v.val}) :
    wireBase N cell c edgeID portID aux v z ≤ guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c := by
  unfold wireBase
  split
  · apply (start_le _ _ _).trans
    change guessedSize N cell c ≤ _
    omega
  · exact Nat.add_le_add_left (start_le _ _ _) _

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
variable {S : Type} [Fintype S] (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
variable (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)

private noncomputable abbrev N := (output e p bin perm positive first q).layout

variable {n s k u C d h w : ℕ} (oldSite : p.layout.Site ↪ Fin s) (oldEdge : p.layout.Edge ↪ Fin k)
variable (seed : S ↪ Fin n) (portID : P ↪ Fin u)
variable (cell : (N e p bin perm positive first q).Site → Fin C)
variable (aux : (N e p bin perm positive first q).Site → ℕ)
variable {τ : Type*} [Fintype τ] (F : Fields (siteCapacity e s n) (edgeCapacity e k n) u C d h w τ)
variable (boxCount : Fin (siteCapacity e s n) → Fin w → τ)
variable (countPin : S × Option (Fin e.count) × Fin w → τ)
variable {x : τ → Bool} (rep : Represents (N e p bin perm positive first q) cell aux
  (siteRows e p oldSite seed) (outputRows e p bin perm positive first q oldEdge seed) portID F x)

include rep in
set_option maxHeartbeats 600000 in
/-- All non-count packet pins are bounded by the maximum of the actual local bit
capacity and the actual number of merged boxes. No positivity of an individual
site or wire width is needed. -/
theorem raw_location_le (U : ℕ) (hw : U < 2^w)
    (cells : ∀ c, let L := N e p bin perm positive first q
      guessedSize L cell c + siteSize L cell c aux + suppliedSize L cell c ≤ U)
    (boxes : ∀ owner, (∑ i : Fin (siteCapacity e s n),
      if value (x ∘ F.owner i) = owner then value (x ∘ boxCount i) else 0) ≤ U)
    (a : S) (z : Σ v : TemplateSite e, Location e v) :
    directoryRaw e seed s k F boxCount countPin x a (.inr z) ≤ U := by
  let L := N e p bin perm positive first q
  let ids := directoryIDs e s k F boxCount
  let counts := Frame.initial countPin
  have fit c := (cells c).trans_lt hw
  have he (r : Raw e) :
      directoryRaw e seed s k F boxCount countPin x a r =
      value (fun j => (install e seed s k counts (CellAddressViews.frame F) ids).eval x (a,r,j)) :=
    (install_value e seed s k counts _ ids x a r).symm
  rcases z with ⟨v,(_ | _ | r)⟩
  · rw [he,installed_site_value e p bin perm positive first q oldSite oldEdge seed portID cell aux F counts ids rep fit]
    let t : L.Site := .inr ⟨a,v⟩
    have hs := siteBase_fits L cell (cell t) (siteRows e p oldSite seed) aux ⟨t,rfl⟩
    have hc := cells (cell t)
    dsimp only at hc
    exact ((Nat.le_add_right _ _).trans hs).trans ((Nat.le_add_right _ _).trans hc)
  · let i := siteSlot e s (seed a) v
    let raw (b : BankBoxOrdinal.Input (siteCapacity e s n) h w) : Bool :=
      b.2.elim (x ∘ F.owner b.1) (x ∘ boxCount b.1)
    have ho (j) : BankBoxOrdinal.ownerWord raw j = value (x ∘ F.owner j) := rfl
    have hc (j) : BankBoxOrdinal.countWord raw j = value (x ∘ boxCount j) := rfl
    have hroom c : (∑ j, if BankBoxOrdinal.ownerWord raw j = c then BankBoxOrdinal.countWord raw j else 0) < 2^w := (boxes c).trans_lt hw
    have hi : value (fun b => ids.eval x (i,b)) = value (fun b => (BankBoxOrdinal.frame _ _ _).eval raw (i,b)) := by
      apply congrArg value
      funext b
      rw [show ids.eval x (i,b) = _ from Frame.subst_eval _ _ _ _]
      congr 1
      funext j
      cases j with
      | mk j tag => cases tag <;> simp [raw,Function.comp_def] <;> rfl
    change value (fun b => ids.eval x (i,b)) ≤ U
    rw [hi,BankBoxOrdinal.frame_value raw hroom]
    refine (Finset.sum_le_sum (s := Finset.univ) (f := fun j =>
      if BankBoxOrdinal.ownerWord raw j = BankBoxOrdinal.ownerWord raw i ∧ j < i then BankBoxOrdinal.countWord raw j else 0)
      (g := fun j => if BankBoxOrdinal.ownerWord raw j = BankBoxOrdinal.ownerWord raw i then BankBoxOrdinal.countWord raw j else 0)
      (fun j _ => by split_ifs <;> omega)).trans (boxes _)
  · cases hr : reference e v r with
    | none =>
      change rawWord e seed s k counts (CellAddressViews.frame F) ids x a (.inr ⟨v,some (some r)⟩) ≤ U
      simp [rawWord,hr]
    | some z =>
      rcases z with ⟨u,side⟩
      rw [he,installed_endpoint_value e p bin perm positive first q oldSite oldEdge seed portID cell aux F counts ids rep fit a v r u side hr]
      cases side <;> exact (wireBase_le L cell _ _ _ aux _ _).trans (cells _)

end Packing.BankJoint

end BorderVNP
end Computability
end OAI
