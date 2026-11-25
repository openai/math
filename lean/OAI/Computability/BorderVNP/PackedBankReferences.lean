import OAI.Computability.BorderVNP.PackedBankJoint
import OAI.Computability.BorderVNP.PackedCellAddressCircuit

/-! # Physical site and cable addresses of the seed packet operands

Selectors and feeders refer to the fixed bank rectangles of the actual sewn
network. An internal paid-site bundle is either one of its one-copy edges or
an attached terminal feeder. The same static endpoint choice works on every
histogram branch, including self-loops.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankJoint

open Crossing Shortening Shortening.StaticRows Shortening.CombiningStep
open ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

private noncomputable def paidReference (a : Fin e.count) (v : (e.net a).Site) :
    PaidBox.Bundle (e.net a) v → Option (TemplateEdge e × Bool)
  | .inl z => some (.inr (.inr ⟨a,z.val⟩),decide ((e.net a).src z.val = v))
  | .inr u => some (.inr (.inl (a,u.val)),false)

/-- Canonical cable and end required by one physical site input. False selects
the destination end, true the source. Unused rectangular pins carry zero. -/
noncomputable def reference : (v : TemplateSite e) → Bases e v → Option (TemplateEdge e × Bool)
  | .inl _, .inl u => some (.inl u,true)
  | .inl _, .inr _ => none
  | .inr (.inl u), .inr (.inl _) => some (.inl u,false)
  | .inr (.inl u), .inr (.inr (.inr a)) => some (.inr (.inl (a,u)),true)
  | .inr (.inl _), _ => none
  | .inr (.inr ⟨a,v⟩), r =>
    paidReference e a v ((Fintype.equivFin (PaidBox.Bundle (e.net a) v)).symm r)

/-- Every physical reference picks an actual endpoint at its own template site. -/
theorem reference_at (v : TemplateSite e) (r : Bases e v) (u : TemplateEdge e) (source : Bool)
    (h : reference e v r = some (u,source)) :
    (if source then templateSrc e u else templateDst e u) = v := by
  rcases v with o | z | ⟨a,v⟩
  · rcases o with ⟨⟩
    rcases r with s | r
    · cases h; rfl
    · cases h
  · rcases r with s | (_ | _ | t)
    · cases h
    · cases h; rfl
    · cases h
    · cases h; rfl
  · change paidReference e a v ((Fintype.equivFin (PaidBox.Bundle (e.net a) v)).symm r) = _ at h
    generalize hz : (Fintype.equivFin (PaidBox.Bundle (e.net a) v)).symm r = z at h
    cases z with
    | inl z =>
      change some (.inr (.inr ⟨a,z.val⟩),decide ((e.net a).src z.val = v)) = some (u,source) at h
      cases h
      by_cases hs : (e.net a).src z.val = v
      · simp [hs,templateSrc]
      · have hd := z.property.resolve_left hs
        simp [hs,hd,templateDst]
    | inr z =>
      change some (.inr (.inl (a,z.val)),false) = some (u,source) at h
      cases h
      simp [templateDst,z.property]

/-- Absolute site slot in the bank rectangle, independent of the input pack. -/
noncomputable def siteSlot {n : ℕ} (old : ℕ) (seed : Fin n) (v : TemplateSite e) :
    Fin (siteCapacity e old n) :=
  finSumFinEquiv (.inr (finProdFinEquiv (seed,Fintype.equivFin (TemplateSite e) v)))

/-- Absolute edge slot after the two hook rectangles and the retained-band rectangle. -/
noncomputable def edgeSlot {n : ℕ} (old : ℕ) (seed : Fin n) (u : TemplateEdge e) :
    Fin (edgeCapacity e old n) :=
  finSumFinEquiv (.inr (finSumFinEquiv (.inr (finProdFinEquiv (seed,Fintype.equivFin (TemplateEdge e) u)))))

/-- The slot read by the public address pass is exactly the seed site's actual stable row. -/
theorem siteSlot_actual {P : Type*} {bits : P → ℕ} (p : Pack D P bits K)
    {A : Type} {s n : ℕ} (old : p.layout.Site ↪ Fin s) (seed : A ↪ Fin n)
    (a : A) (v : TemplateSite e) : siteSlot e s (seed a) v = siteRows e p old seed (.inr ⟨a,v⟩) := rfl

/-- The slot queried for a selector, feeder or internal cable is its true physical
row in every branch, regardless of the count vector. -/
theorem edgeSlot_actual [NeZero D] {P : Type*} {bits : P → ℕ} (p : Pack D P bits K)
    {A : Type} [Fintype A] (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
    {k n : ℕ} (old : p.layout.Edge ↪ Fin k) (seed : A ↪ Fin n) (a : A) (u : TemplateEdge e) :
    edgeSlot e k (seed a) u = outputRows e p bin perm positive first q old seed (.inr (.inr ⟨a,u⟩)) := rfl

/-- The actual owner site of the selected end of the sewn edge. -/
theorem reference_site [NeZero D] {P : Type*} {bits : P → ℕ} (p : Pack D P bits K)
    {A : Type} [Fintype A] (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
    (a : A) (v : TemplateSite e) (r : Bases e v) (u : TemplateEdge e) (source : Bool)
    (h : reference e v r = some (u,source)) :
    let L := (output e p bin perm positive first q).layout
    let edge : L.Edge := .inr (.inr ⟨a,u⟩)
    (if source then L.src edge else L.dst edge) = .inr ⟨a,v⟩ := by
  have he := reference_at e v r u source h
  have hf := bank_fields e p bin perm positive first q a u
  cases source
  · change templateDst e u = v at he
    exact hf.2.1.trans (congrArg (fun z => (Sum.inr ⟨a,z⟩ : SiteShape e p A)) he)
  · change templateSrc e u = v at he
    exact hf.1.trans (congrArg (fun z => (Sum.inr ⟨a,z⟩ : SiteShape e p A)) he)

end Packing.BankJoint

end BorderVNP
end Computability
end OAI
