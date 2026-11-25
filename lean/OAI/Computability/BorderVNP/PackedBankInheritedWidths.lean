import OAI.Computability.BorderVNP.PackedBankInheritedRead

/-! # Cable and external port widths at an inherited site

Each band of an incident input cable has its own physical wire in the combining
output. For a selected loop the old table reads the source hook, so the second
hook can increase the total physical width. Every external port keeps its width
and its inherited attachment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedBank

open Crossing Shortening Shortening.CombiningStep Shortening.SeedIntervals Inherited
open scoped BigOperators Classical

variable {D : ℕ} {P : Type*} {bits : P → ℕ}

/-- Total width of the distinct cables incident at a site, counting a loop once. -/
noncomputable def incidentWidth (N : Network D P bits) (v : N.Site) : ℕ :=
  ∑ c : Incident N v, N.width c.val

/-- Total width of the external ports attached to a site. -/
noncomputable def portWidth [Fintype P] (N : Network D P bits) (v : N.Site) : ℕ :=
  ∑ t : {t : P // N.attach t = v}, bits t.val

variable {m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    (p : Pack D P bits K) {A : Type} [Fintype A] (bin : p.layout.Edge → Option A)
    (perm : Fin D → Equiv.Perm A) (positive : p.layout.Edge → Bool) (first : Fin D × Bool)
    (q : Counts e p bin perm) (v : p.layout.Site)

/-- A retained wire or a chosen hook remembers both the original cable and its band. -/
theorem oldBandWire_injective :
    Function.Injective (fun s : Incident p.layout v × Band D =>
      oldBandWire e p bin perm positive first q v s.1 s.2) := by
  let G := (output e p bin perm positive first q).layout
  let recover : G.Edge → Option (p.layout.Edge × Band D) :=
    Sum.elim (Sum.elim (fun z => some z.val) (fun z => some z.val))
      (Sum.elim (fun z => some z.val) (fun _ => none))
  have decodes (c : Incident p.layout v) (b : Band D) :
      recover (oldBandWire e p bin perm positive first q v c b).val = some (c.val,b) := by
    unfold oldBandWire
    split
    · split <;> rfl
    · rfl
  rintro ⟨c,b⟩ ⟨c',b'⟩ h
  have hpair := Option.some.inj ((decodes c b).symm.trans
    ((congrArg (fun z : Incident G (.inl v) => recover z.val) h).trans (decodes c' b')))
  have hb : b = b' := congrArg Prod.snd hpair
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hpair)) hb

/-- The physical cables at the inherited site contain all incident input bits. -/
theorem output_incidentWidth_le : incidentWidth p.layout v ≤
    incidentWidth (output e p bin perm positive first q).layout (.inl v) := by
  let bandWidth (s : Incident p.layout v × Band D) :=
    (layout p.layout bin perm m).width (s.1.val,s.2)
  have sumWidth : (∑ s, bandWidth s) = incidentWidth p.layout v := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun c _ => p.layout.sum_bands_width (label p.layout bin perm m) c.val
  rw [← sumWidth]
  exact Finset.sum_le_sum_of_injOn _ (oldBandWire_injective e p bin perm positive first q v).injOn
    (Finset.subset_univ _) (fun s _ => (oldBandWire_width e p bin perm positive first q v s.1 s.2).symm.le)
    (fun _ _ _ => Nat.zero_le _)

/-- The output has precisely the original external port width at each inherited site. -/
theorem output_portWidth [Fintype P] :
    portWidth (output e p bin perm positive first q).layout (.inl v) = portWidth p.layout v := by
  let G := (output e p bin perm positive first q).layout
  let ports : {t : P // G.attach t = .inl v} ≃ {t : P // p.layout.attach t = v} :=
    Equiv.subtypeEquivRight fun _ => ⟨Sum.inl.inj,congrArg Sum.inl⟩
  exact Fintype.sum_equiv ports _ _ fun _ => rfl

end Packing.InheritedBank

end BorderVNP
end Computability
end OAI
