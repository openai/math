import OAI.Computability.BorderVNP.PackedInheritedProfileState

/-! # Virtual singleton banks at newly inserted profile sites

An origin or a terminal has no self-loop, so its entire internal-guess block
is empty. Its unique site's work bits begin at zero, followed by the supplied
incidence words. These addresses and lookup semantics implement the finite
intrinsic site bank used by subsequent rounds.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedProfile

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Inherited BankSite CellAddresses CellSparse
open scoped Classical

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (v : N.Site) (aux : N.Site → ℕ) {ns ne np : ℕ} (siteID : N.Site ↪ Fin ns)
variable (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)

omit [Fintype P] in
/-- The one site's staging block in its own virtual cell has precisely its own work length. -/
theorem singleton_size : siteSize N id v aux = aux v := by
  let : Unique {u : N.Site // id u = v} := ⟨⟨⟨v,rfl⟩⟩,fun z => Subtype.ext z.property⟩
  exact Fintype.sum_unique (fun z : {u : N.Site // id u = v} => aux z.val)

omit [Fintype P] in
/-- In a virtual cell with no internal wire bits the site's work starts at zero. -/
theorem singleton_start (empty : guessedSize N id v = 0) :
    siteBase N id v siteID aux ⟨v,rfl⟩ = 0 := by
  rw [siteBase,empty,zero_add,CellSlabs.start]
  apply Finset.sum_eq_zero
  intro z _
  obtain rfl : z = ⟨v,rfl⟩ := Subtype.ext z.property
  simp

/-- Any incident cable's physical port follows the site's work block at its
stable incidence address, including the case that the cable width vanishes. -/
theorem singleton_wire (noLoop : ∀ z : Incident N v, N.src z.val ≠ N.dst z.val) (z : Incident N v) :
    wireBase N id v edgeID portID aux ⟨v,rfl⟩ z = aux v+wireStart N edgeID portID v z := by
  simp only [wireStart,wireBase,id_eq,noLoop z,dite_false,externalBase,singleton_size,add_zero]
  omega

variable {m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {S : Type} [Fintype S] (p : Pack D P bits K) (bin : p.layout.Edge → Option S)
variable (perm : Fin D → Equiv.Perm S) (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
private noncomputable abbrev G := (output e p bin perm positive first q).layout
variable (a : S)

/-- A physical origin or terminal, excluding the paid one-copy sites. -/
def profileNode : Unit ⊕ (Fin D × Bool) → TemplateSite e
  | .inl u => .inl u
  | .inr t => .inr (.inl t)

omit [Fintype P] in
/-- Every wire incident to a new profile origin or terminal joins two distinct
sites, including selected hooks attached to an old self-loop. -/
theorem profile_noLoop (r : Unit ⊕ (Fin D × Bool)) :
    let v := seedSite e p bin perm positive first q a (profileNode e r)
    ∀ z : Incident (G e p bin perm positive first q) v,
      (G e p bin perm positive first q).src z.val ≠ (G e p bin perm positive first q).dst z.val := by
  intro v z h
  have hs := z.property.elim id (h.trans ·)
  obtain ⟨z,hz⟩ := z
  rcases z with z | z | ⟨s,z⟩
  · cases h
  · dsimp only [v,seedSite] at hs
    cases hs
  · have hf := bank_fields e p bin perm positive first q s z
    change (G e p bin perm positive first q).src (.inr (.inr ⟨s,z⟩)) = _ at hs h
    rw [hf.1,hf.2.1] at h
    rw [hf.1] at hs
    rcases z with t | ⟨u,t⟩ | ⟨u,c⟩
    · cases h
    · cases h
    · rcases r with ⟨⟩ | t <;> dsimp only [v,seedSite,profileNode,templateSrc] at hs <;> cases hs

omit [Fintype P] in
/-- The virtual internal block at a profile site is empty. -/
theorem profile_empty (r : Unit ⊕ (Fin D × Bool)) :
    let v := seedSite e p bin perm positive first q a (profileNode e r)
    guessedSize (G e p bin perm positive first q) id v = 0 := by
  intro v
  apply Finset.sum_eq_zero
  intro z _
  exact False.elim (profile_noLoop e p bin perm positive first q a r ⟨z.val,.inl z.property.1⟩
    (z.property.1.trans z.property.2.symm))

end Packing.InheritedProfile

end BorderVNP
end Computability
end OAI
