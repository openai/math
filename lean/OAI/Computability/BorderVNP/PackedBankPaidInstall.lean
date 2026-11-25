import OAI.Computability.BorderVNP.PackedBankBoxPhysical
import OAI.Computability.BorderVNP.PackedBankInstalledAddresses

/-! # The installed public directory supplies the actual paid-site fragment

The stable site row supplies the staging offset and merged box ID. For each
incident bundle the endpoint pass chooses an end belonging to the site,
including at a loop. Therefore the full serialized record list generated
by the public stage is the list verified by the private physical-site proof.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.PaidPhysical

open Crossing Shortening Shortening.StaticRows Shortening.CombiningStep
open BankJoint CellAddressPhysical CellAddressCircuit CellAddresses ParseBatchSort VPVNP.VerifierNetwork
open private paidReference from OAI.Computability.BorderVNP.PackedBankReferences
open scoped Classical

private theorem ownerBase {D edges ports : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    {C : Type} (cell : N.Site → C) (edgeID : N.Edge ↪ Fin edges) (portID : P ↪ Fin ports)
    (aux : N.Site → ℕ) (v : N.Site) (z : {z : N.Edge // N.src z = v ∨ N.dst z = v})
    (name : N.Edge) (hn : z.val = name) (side : Bool) (h : (if side then N.src name else N.dst name) = v) :
    (if side then wireBase N cell (cell (N.src name)) edgeID portID aux ⟨N.src name,rfl⟩ ⟨name,.inl rfl⟩
      else wireBase N cell (cell (N.dst name)) edgeID portID aux ⟨N.dst name,rfl⟩ ⟨name,.inr rfl⟩) =
        wireBase N cell (cell v) edgeID portID aux ⟨v,rfl⟩ z := by
  subst name
  rcases z with ⟨z,hz⟩
  cases side <;> dsimp only [Bool.false_eq_true,ite_false,ite_true] at h ⊢ <;> subst v <;> rfl

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
    {S : Type} [Fintype S] (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)

private noncomputable abbrev N := (output e p bin perm positive first q).layout

variable {n s k u C d h w : ℕ} (oldSite : p.layout.Site ↪ Fin s) (oldEdge : p.layout.Edge ↪ Fin k)
    (seed : S ↪ Fin n) (portID : P ↪ Fin u) (cell : (N e p bin perm positive first q).Site → Fin C)
    (aux : (N e p bin perm positive first q).Site → ℕ)
    {σ : Type*} [Fintype σ] (F : Fields (siteCapacity e s n) (edgeCapacity e k n) u C d h w σ)
    (counts : Frame σ (S × Option (Fin e.count) × Fin w))
    (ids : Frame σ (Fin (siteCapacity e s n) × Fin w)) {x : σ → Bool}
    (rep : Represents (N e p bin perm positive first q) cell aux (siteRows e p oldSite seed)
      (outputRows e p bin perm positive first q oldEdge seed) portID F x)
    (fit : ∀ c, let G := N e p bin perm positive first q
      guessedSize G cell c + siteSize G cell c aux + suppliedSize G cell c < 2^w)

include rep fit in
/-- Each actual operand of the canonical paid-site cable-base array is the
corresponding output of the installed geometry/address frame. -/
theorem installed_paidBase (t : S) (a : Fin e.count) (v : (e.net a).Site)
    (r : Fin (Fintype.card (PaidBox.Bundle (e.net a) v))) :
    rawWord e seed s k counts (CellAddressViews.frame F) ids x t
      (.inr ⟨.inr (.inr ⟨a,v⟩),some (some r)⟩) =
      bases e p bin perm positive first q t a v cell (outputRows e p bin perm positive first q oldEdge seed) portID aux r := by
  let V : TemplateSite e := .inr (.inr ⟨a,v⟩)
  let G := N e p bin perm positive first q
  let here : G.Site := .inr ⟨t,V⟩
  let B := PaidBox.Bundle (e.net a) v
  let code (z : B) : TemplateEdge e × Bool := match z with
    | .inl z => (.inr (.inr ⟨a,z.val⟩),decide ((e.net a).src z.val = v))
    | .inr u => (.inr (.inl (a,u.val)),false)
  let z := (Fintype.equivFin B).symm r
  let E := cable e p bin perm positive first q t a v z
  have href : reference e V r = some (code z) := by
    change paidReference e a v z = some (code z)
    cases z <;> rfl
  have hz : E.val = .inr (.inr ⟨t,(code z).1⟩) := by change (cable _ _ _ _ _ _ _ _ _ _ z).val = _; cases z <;> rfl
  have hs := reference_site e p bin perm positive first q t V r (code z).1 (code z).2 href
  have he := installed_endpoint_value e p bin perm positive first q oldSite oldEdge seed portID cell aux F counts ids rep fit t V r
    (code z).1 (code z).2 href
  rw [install_value] at he
  rw [he]
  change (if (code z).2 then wireBase G cell _ _ portID aux _ _ else wireBase G cell _ _ portID aux _ _) = _
  exact ownerBase G cell (outputRows e p bin perm positive first q oldEdge seed) portID aux here E
    (.inr (.inr ⟨t,(code z).1⟩)) hz (code z).2 hs

include rep fit in
/-- The frozen public packet generator produces exactly the private paid fragment at
the site offset, box-ID frame output, public count word, and shared cable bases. -/
theorem emitted_fragment (t : S) (a : Fin e.count) (v : (e.net a).Site)
    (hc : value (fun b => counts.eval x (t,some a,b)) = (q t).val a)
    (boxes : List (List CellSparse.Factor)) :
    let G := N e p bin perm positive first q
    let V : TemplateSite e := .inr (.inr ⟨a,v⟩)
    let here : G.Site := .inr ⟨t,V⟩
    let raw := rawWord e seed s k counts (CellAddressViews.frame F) ids x t
    let off := siteBase G cell (cell here) (siteRows e p oldSite seed) aux ⟨here,rfl⟩
    let id := value (fun b => ids.eval x (siteSlot e s (seed t) V,b))
    let physical := bases e p bin perm positive first q t a v cell (outputRows e p bin perm positive first q oldEdge seed) portID aux
    emitted e first raw V = (PaidBinding.fragment (PaidBox.widths (e.net a) v) ((q t).val a) off id physical boxes).records := by
  intro G V here raw off id physical
  have hs := installed_site_value e p bin perm positive first q oldSite oldEdge seed portID cell aux F counts ids rep fit t V
  rw [install_value] at hs
  have fields : (fun i : Operands e V => word e raw (pin e V i)) =
      PaidBinding.fields (PaidBox.widths (e.net a) v) ((q t).val a) off id physical := by
    funext i
    rcases i with _ | _ | h | r
    · exact hs
    · rfl
    · exact congrArg (fun c => PaidBox.header (PaidBox.widths (e.net a) v) c h) hc
    · exact installed_paidBase e p bin perm positive first q oldSite oldEdge seed portID cell aux F counts ids rep fit t a v r
  change (BankPacket.Paid.rows _).map (BankPacket.RecordCode.read (fun i : Operands e V => word e raw (pin e V i))) = _
  rw [fields]
  rfl

end Packing.PaidPhysical

end BorderVNP
end Computability
end OAI
