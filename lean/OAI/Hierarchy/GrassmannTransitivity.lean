import OAI.Computability.VPVNP.GrassmannTypes
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.ModularLattice
import Mathlib.Tactic

namespace OAI
/-! # Transitivity of the binary linear group on Grassmann pairs -/

namespace Hierarchy.GrassmannTransitivity

open Computability.VPVNP.Grassmann
open LinearMap Submodule

structure Split {m : ℕ} (a b : Plane m) where
  common : Submodule (ZMod 2) (Space m)
  left : Submodule (ZMod 2) (Space m)
  right : Submodule (ZMod 2) (Space m)
  intersection : common = a.val ⊓ b.val
  sum_left : common ⊔ left = a.val
  sum_right : common ⊔ right = b.val
  disjoint_left : Disjoint common left
  disjoint_right : Disjoint a.val right

theorem split_exists {m : ℕ} (a b : Plane m) : Nonempty (Split a b) := by
  obtain ⟨L, hL, hLA⟩ := IsModularLattice.exists_disjoint_and_sup_eq (inf_le_left : a.val ⊓ b.val ≤ a.val)
  obtain ⟨R, hR, hRB⟩ := IsModularLattice.exists_disjoint_and_sup_eq (inf_le_right : a.val ⊓ b.val ≤ b.val)
  have hRb : R ≤ b.val := hRB ▸ le_sup_right
  refine ⟨⟨_,L,R,rfl,hLA,hRB,hL,?_⟩⟩
  rw [disjoint_iff, ← inf_of_le_right hRb, ← inf_assoc, hR.eq_bot]

abbrev Split.embed {m : ℕ} {a b : Plane m} (s : Split a b) :=
  (s.common.subtype.coprod s.left.subtype).coprod s.right.subtype

theorem Split.injective {m : ℕ} {a b : Plane m} (s : Split a b) :
    Function.Injective s.embed := by
  have h : Disjoint (range (s.common.subtype.coprod s.left.subtype)) (range s.right.subtype) := by
    simpa only [range_coprod, range_subtype, s.sum_left] using s.disjoint_right
  have h' : Disjoint (range s.common.subtype) (range s.left.subtype) := by
    simpa only [range_subtype] using s.disjoint_left
  rw [← ker_eq_bot, Split.embed, ker_coprod_of_disjoint_range _ _ h,
    ker_coprod_of_disjoint_range _ _ h']
  simp

theorem Split.ranks {m r : ℕ} {a b : Plane m} (h : HasType r a b) (s : Split a b) :
    Module.finrank (ZMod 2) s.common = m-r ∧ Module.finrank (ZMod 2) s.left = r ∧
    Module.finrank (ZMod 2) s.right = r := by
  have hi := finrank_sup_add_finrank_inf_eq a.val b.val
  rw [show Module.finrank (ZMod 2) (a.val ⊔ b.val : Submodule _ _) = _ from h,
    ← s.intersection, a.property, b.property] at hi
  have hL := finrank_sup_add_finrank_inf_eq s.common s.left
  have hR := finrank_sup_add_finrank_inf_eq s.common s.right
  have hsub : s.common ≤ a.val := s.sum_left ▸ le_sup_left
  rw [s.sum_left, s.disjoint_left.eq_bot, finrank_bot, a.property] at hL
  rw [s.sum_right, (s.disjoint_right.mono_left hsub).eq_bot, finrank_bot, b.property] at hR
  omega

/-- The action is transitive on ordered pairs with prescribed sum dimension. -/
theorem pair_transitive {m r : ℕ} (p q : Pair m r) : ∃ g : Computability.VPVNP.Grassmann.GL m, g • p = q := by
  classical
  obtain ⟨s⟩ := split_exists p.val.1 p.val.2
  obtain ⟨t⟩ := split_exists q.val.1 q.val.2
  obtain ⟨hs0, hs1, hs2⟩ := s.ranks p.property
  obtain ⟨ht0, ht1, ht2⟩ := t.ranks q.property
  let e := LinearEquiv.ofFinrankEq s.common t.common (hs0.trans ht0.symm)
  let f := LinearEquiv.ofFinrankEq s.left t.left (hs1.trans ht1.symm)
  let k := LinearEquiv.ofFinrankEq s.right t.right (hs2.trans ht2.symm)
  let u := LinearEquiv.ofInjective s.embed s.injective
  let v := LinearEquiv.ofInjective t.embed t.injective
  let l := u.symm.trans (((e.prodCongr f).prodCongr k).trans v)
  obtain ⟨g,hg⟩ := Submodule.exists_linearEquiv_restrict_eq l
  have h (x : s.common) (y : s.left) (z : s.right) :
      g ((x : Space m) + y + z) = (e x : Space m) + f y + k z := by
    have hh := hg (u ((x,y),z))
    have heq : g ↑(u ((x,y),z)) = ↑(v ((e x,f y),k z)) := by simpa [l] using hh.symm
    exact heq
  have hc : s.common.map g.toLinearMap = t.common := by
    ext a
    constructor
    · rintro ⟨b,hb,rfl⟩
      simpa using (show g (b + (0:s.left) + (0:s.right)) ∈ t.common by
        rw [h ⟨b,hb⟩ 0 0]; simp)
    · intro ha
      obtain ⟨b,hb⟩ := e.surjective ⟨a,ha⟩
      refine ⟨b,b.property,?_⟩
      simpa [hb] using h b 0 0
  have hleft : s.left.map g.toLinearMap = t.left := by
    ext a
    constructor
    · rintro ⟨b,hb,rfl⟩
      simpa using (show g ((0:s.common) + b + (0:s.right)) ∈ t.left by
        rw [h 0 ⟨b,hb⟩ 0]; simp)
    · intro ha
      obtain ⟨b,hb⟩ := f.surjective ⟨a,ha⟩
      refine ⟨b,b.property,?_⟩
      simpa [hb] using h 0 b 0
  have hright : s.right.map g.toLinearMap = t.right := by
    ext a
    constructor
    · rintro ⟨b,hb,rfl⟩
      simpa using (show g ((0:s.common) + (0:s.left) + b) ∈ t.right by
        rw [h 0 0 ⟨b,hb⟩]; simp)
    · intro ha
      obtain ⟨b,hb⟩ := k.surjective ⟨a,ha⟩
      refine ⟨b,b.property,?_⟩
      simpa [hb] using h 0 0 b
  refine ⟨g,Subtype.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))⟩
  · change p.val.1.val.map g.toLinearMap = q.val.1.val
    rw [← s.sum_left, Submodule.map_sup, hc, hleft, t.sum_left]
  · change p.val.2.val.map g.toLinearMap = q.val.2.val
    rw [← s.sum_right, Submodule.map_sup, hc, hright, t.sum_right]

end Hierarchy.GrassmannTransitivity

end OAI
