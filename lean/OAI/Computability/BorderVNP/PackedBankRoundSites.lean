import OAI.Computability.BorderVNP.PackedBankProfileBirthCharges
import OAI.Computability.BorderVNP.PackedInheritedPaidModel

/-! # The site programs installed by a complete selected crossing round

Each retained site's next cut list comes in the public pass's actual order.
All newly inserted origin, terminal and paid sites use their intrinsic physical
programs. The exact programs satisfy the cumulative physical load recurrence.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening Shortening.StaticRows Shortening.SeedIntervals Shortening.CombiningStep
  InheritedBank InheritedProfile CellSparse
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
  {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
  (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
  (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
  (binName : S → ℕ) (position : e.Entry → ℕ)

private noncomputable abbrev L := (output e p bin perm positive first q).layout

variable {ns ne np : ℕ} (siteID : (L e p bin perm positive first q).Site ↪ Fin ns)
  (edgeID : (L e p bin perm positive first q).Edge ↪ Fin ne) (portID : P ↪ Fin np)
  (old : p.layout.Site → Site) (cuts : p.layout.Site → List Slice)

/-- The actual persistent programs at all sites of the chosen physical output.
Retained interval lists may be supplied in the stable public sort order. -/
noncomputable def roundSites : (L e p bin perm positive first q).Site → Site
  | .inl v => (old v).retain (incoming (L e p bin perm positive first q) (.inl v)) (cuts v)
  | .inr ⟨a,.inl _⟩ => originSite e p bin perm positive first q a siteID edgeID portID
  | .inr ⟨a,.inr (.inl t)⟩ => terminalSite e p bin perm positive first q a siteID edgeID portID binName t
  | .inr ⟨a,.inr (.inr ⟨i,v⟩)⟩ => PaidSite.physical e p bin perm positive first q a i v edgeID portID position

private noncomputable abbrev installed := roundSites e p bin perm positive first q binName position siteID edgeID portID old cuts

/-- Each stored program's current input area has the exact physical size of
its incident cable and external port words. -/
theorem roundSites_incoming (v : (L e p bin perm positive first q).Site) :
    (installed e p bin perm positive first q binName position siteID edgeID portID old cuts v).incoming =
      incoming (L e p bin perm positive first q) v := by
  rcases v with v | ⟨a,(_ | _ | ⟨i,v⟩)⟩ <;> rfl

set_option maxRecDepth 3000 in
set_option backward.isDefEq.respectTransparency false in
/-- The full syntax and expanded work/visit count of every installed program
fit the cumulative fields on this physical layout. Only the length of the
stable cut list enters the size bound. -/
theorem roundSites_charged (prior payload : p.layout.Site → ℕ)
    (hin : ∀ v, (old v).incoming = incoming p.layout v)
    (hold : ∀ v, (old v).staticNodes ≤ prior v ∧ (old v).expandedLoad ≤ payload v)
    (hlen : ∀ v, (cuts v).length = tieRows (L e p bin perm positive first q)
      (gathered e p bin perm positive first q (.inl v)) (.inl v))
    (v : (L e p bin perm positive first q).Site) :
    let s := installed e p bin perm positive first q binName position siteID edgeID portID old cuts v
    s.staticNodes ≤ nextPrior e p bin perm positive first q prior v ∧
      s.expandedLoad ≤ nextPayload e p bin perm positive first q payload v := by
  change SiteShape e p S at v
  rcases v with v | ⟨a,(_ | t | ⟨i,v⟩)⟩
  · dsimp only [installed,roundSites,nextPrior,Sum.elim_inl,nextPayload]
    rw [(old v).staticNodes_retain,(old v).expandedLoad_retain,hlen v,hin v,incoming_eq_widths p.layout v]
    exact ⟨Nat.add_le_add (hold v).1 (Nat.mul_le_mul_right _ (by decide)),Nat.add_le_add_right (hold v).2 _⟩
  · obtain ⟨hs,hv⟩ := origin_charges e p bin perm positive first q a siteID edgeID portID
    exact ⟨hs.le.trans (Nat.le_add_right _ _),hv.le⟩
  · exact terminal_within e p bin perm positive first q a siteID edgeID portID binName t prior payload
  · have h := PaidSite.born_charges e position first i v (blocks p.layout bin perm m a) (q a).val
      (incoming (L e p bin perm positive first q) (.inr ⟨a,.inr (.inr ⟨i,v⟩)⟩))
      (PaidSite.starts e p bin perm positive first q a i v edgeID portID)
    exact ⟨h.1.le.trans (Nat.le_add_right _ _),h.2.le⟩

/-- Every ordering of the canonical emitted cut list has the required physical
length, without any gate assumption concerning the classical cable enumeration. -/
theorem cuts_length_of_perm {oldE : ℕ} (oldID : p.layout.Edge ↪ Fin oldE)
    (sorted : ∀ v, (cuts v).Perm (layerCuts e p bin perm binName positive first q v oldID edgeID portID)) (v : p.layout.Site) :
    (cuts v).length = tieRows (L e p bin perm positive first q)
      (gathered e p bin perm positive first q (.inl v)) (.inl v) :=
  (sorted v).length_eq.trans (layerCuts_length portID e p bin perm binName positive first q v oldID edgeID)

/-- For an actual region, the retained and fresh sparse programs have the
fixed-factor resource bound of the selected crossing's physical records. -/
theorem roundSites_load_le (ex : Bool) (prior payload : p.layout.Site → ℕ)
    (hin : ∀ v, (old v).incoming = incoming p.layout v)
    (hold : ∀ v, (old v).staticNodes ≤ prior v ∧ (old v).expandedLoad ≤ payload v)
    (hlen : ∀ v, (cuts v).length = tieRows (L e p bin perm positive first q)
      (gathered e p bin perm positive first q (.inl v)) (.inl v))
    (test : (L e p bin perm positive first q).Site → Prop) :
    let N := L e p bin perm positive first q
    let site := installed e p bin perm positive first q binName position siteID edgeID portID old cuts
    localRecords N ex (fun v => (site v).staticNodes) (fun v => (site v).expandedLoad) test ≤
      loadMultiplier e * localRecords N ex (Sum.elim prior (fun _ => 0))
        (Sum.elim payload (fun z => bankUses e (blocks p.layout bin perm m z.1) (q z.1).val z.2)) test := by
  intro N site
  refine le_trans ?_ (output_load_le e p bin perm positive first q ex prior payload test)
  unfold localRecords
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  apply Finset.sum_le_sum
  intro v _
  have ⟨hs,hp⟩ := roundSites_charged e p bin perm positive first q binName position siteID edgeID portID
    old cuts prior payload hin hold hlen v
  by_cases ht : test v
  · simp only [ht,ite_true]
    cases ex
    · exact Nat.add_le_add_right hs _
    · exact Nat.add_le_add hs (Nat.add_le_add_left hp 1)
  · simp only [ht,ite_false,le_refl]

end Packing.Inherited

end BorderVNP
end Computability
end OAI
