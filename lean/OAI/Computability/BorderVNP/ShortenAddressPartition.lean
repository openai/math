import OAI.Computability.BorderVNP.ShortenNetworkBundle
import OAI.Computability.BorderVNP.CrossingParallel

/-!
# Simultaneous replacements at disjoint seed addresses

A seed partition tags each matched interval at both its old endpoints. The
tensor of a disjoint union of profile networks is their ordinary product,
including when their widths and port sets differ from seed to seed.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Crossing
open scoped BigOperators Classical

variable {D : ℕ} {P : Type*} {bits : P → ℕ} {N : Network D P bits}
variable {A : Type} [Fintype A]

/-- Selected cables grouped by seed address. -/
structure AddressPartition (N : Network D P bits) (A : Type) where
  /-- Matched intervals for each seed. -/
  part : A → Finset N.Edge
  /-- A matched interval belongs to just one seed. -/
  unique : ∀ {a b c}, c ∈ part a → c ∈ part b → a = b

namespace AddressPartition

variable (t : AddressPartition N A)

/-- All matched intervals in a combining step. -/
noncomputable def selected : Finset N.Edge := Finset.univ.biUnion t.part

/-- Regard one seed's selected interval as a globally selected interval. -/
def includeEdge (a : A) (e : ↥(t.part a)) : ↥t.selected :=
  ⟨e.val, Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, e.property⟩⟩

/-- Including all tagged interval names gives a bijection onto the global names. -/
noncomputable def edgeIndex : (Σ a, ↥(t.part a)) ≃ ↥t.selected :=
  Equiv.ofBijective (fun e => t.includeEdge e.1 e.2) <| by
    constructor
    · rintro ⟨a,e⟩ ⟨b,f⟩ h
      have hval : e.val = f.val := congrArg Subtype.val h
      obtain rfl := t.unique e.property (hval ▸ f.property)
      congr 1; exact Subtype.ext hval
    · rintro ⟨e, he⟩
      obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp he
      exact ⟨⟨a, e, ha⟩, rfl⟩

/-- A port at one seed retains its old source/destination slot. -/
def includePort (a : A) : N.CutPorts (t.part a) → N.CutPorts t.selected :=
  Sum.map (t.includeEdge a) (t.includeEdge a)

/-- The union of local slot names gives a bijection onto all the cut ends. -/
noncomputable def portIndex : (Σ a, N.CutPorts (t.part a)) ≃ N.CutPorts t.selected :=
  Equiv.ofBijective (fun q => t.includePort q.1 q.2) <| by
    constructor
    · rintro ⟨a, u | u⟩ ⟨b, v | v⟩ h
      · have he : (⟨a,u⟩ : Σ a, ↥(t.part a)) = ⟨b,v⟩ :=
          t.edgeIndex.injective (Sum.inl.inj h)
        cases he
        rfl
      · cases h
      · cases h
      · have he : (⟨a,u⟩ : Σ a, ↥(t.part a)) = ⟨b,v⟩ :=
          t.edgeIndex.injective (Sum.inr.inj h)
        cases he
        rfl
    · rintro (e | e) <;> obtain ⟨⟨a,u⟩, he⟩ := t.edgeIndex.surjective e
      · exact ⟨⟨a,.inl u⟩, congrArg Sum.inl he⟩
      · exact ⟨⟨a,.inr u⟩, congrArg Sum.inr he⟩

/-- Read a seed's interval words from the joint vector of cut slots. -/
def inputs (s : Ports (N.cutWidths t.selected)) (a : A) : Ports (N.cutWidths (t.part a))
  | .inl e => s (.inl (t.includeEdge a e))
  | .inr e => s (.inr (t.includeEdge a e))

/-- The joint wire tensor is exactly the product of the wire equalities at the seeds. -/
theorem equality_product {R : Type*} [CommSemiring R] (s : Ports (N.cutWidths t.selected)) :
    N.cutEquality t.selected s = ∏ a, (N.cutEquality (t.part a) (t.inputs s a) : R) := by
  unfold Network.cutEquality
  rw [Fintype.prod_boole]
  have he : ((fun e : ↥t.selected => s (.inl e)) = fun e => s (.inr e)) ↔
      ∀ a, (fun e : ↥(t.part a) => t.inputs s a (.inl e)) = fun e => t.inputs s a (.inr e) := by
    constructor
    · intro h a; funext e; exact congrFun h (t.includeEdge a e)
    · intro h; funext e
      obtain ⟨⟨a,u⟩, rfl⟩ := t.edgeIndex.surjective e
      exact congrFun (h a) u
  by_cases h : (fun e : ↥t.selected => s (.inl e)) = fun e => s (.inr e)
  · rw [ite_eq_left h, ite_eq_left (he.mp h)]
  · rw [ite_eq_right h, ite_eq_right (mt he.mpr h)]

variable (G : ∀ a, Network D (N.CutPorts (t.part a)) (N.cutWidths (t.part a)))

/-- Disjoint union of the seed gadgets, exposing ports indexed by the global cut. -/
noncomputable def parallel : Network D (N.CutPorts t.selected) (N.cutWidths t.selected) where
  Site := Σ a, (G a).Site
  Edge := Σ a, (G a).Edge
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src e := ⟨e.1, (G e.1).src e.2⟩
  dst e := ⟨e.1, (G e.1).dst e.2⟩
  width e := (G e.1).width e.2
  attach q := let z := t.portIndex.symm q; ⟨z.1, (G z.1).attach z.2⟩
  position v := (G v.1).position v.2
  in_ball v := (G v.1).in_ball v.2

/-- The global port for a local endpoint still attaches at that endpoint's chosen site. -/
theorem attach_include (a : A) (q : N.CutPorts (t.part a)) :
    (t.parallel G).attach (t.includePort a q) = ⟨a, (G a).attach q⟩ := by
  let attach := fun z : Σ a, N.CutPorts (t.part a) => (⟨z.1, (G z.1).attach z.2⟩ : Σ a, (G a).Site)
  exact congrArg attach (t.portIndex.symm_apply_apply ⟨a,q⟩)

variable {R : Type*} [CommSemiring R]

/-- Tables on the disjoint union read only the tagged local cables and old endpoint slots. -/
noncomputable def parallelTables (table : ∀ a, (G a).Tables R) : (t.parallel G).Tables R := by
  intro v z x
  rcases v with ⟨a,v⟩
  apply table a v
  · intro e; exact z ⟨⟨a,e.val⟩, e.property.imp (congrArg (Sigma.mk a)) (congrArg (Sigma.mk a))⟩
  · rintro ⟨q | q, h⟩
    · exact x ⟨t.includePort a (.inl q), (t.attach_include G a _).trans (congrArg (Sigma.mk a) h)⟩
    · exact x ⟨t.includePort a (.inr q), (t.attach_include G a _).trans (congrArg (Sigma.mk a) h)⟩

/-- Actual independent assignments at each seed factor the tensor of their parallel union. -/
theorem parallel_value (table : ∀ a, (G a).Tables R) (s : Ports (N.cutWidths t.selected)) :
    (t.parallel G).value (t.parallelTables G table) s =
      ∏ a, (G a).value (table a) (t.inputs s a) := by
  let e : (t.parallel G).Assignment ≃ ∀ a, (G a).Assignment :=
    Equiv.piCurry fun a (c : (G a).Edge) => Fin ((G a).width c) → Bool
  unfold Network.value
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv e
  intro z
  refine (Fintype.prod_sigma (fun v : Σ a, (G a).Site =>
    (t.parallel G).read (t.parallelTables G table) z s v)).trans ?_
  apply Finset.prod_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro v _
  apply congrArg (table a v _)
  funext q
  rcases q with ⟨q | q, h⟩ <;> rfl

end AddressPartition
end Shortening

end BorderVNP
end Computability
end OAI
