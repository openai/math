import OAI.Computability.BorderVNP.CrossingNetwork

/-!
# Replacing subnetworks with arbitrary exterior factors

The cables between a subnetwork and its exterior become ordinary shared edges
when the two are sewn together. Every external index of the subnetwork is summed
once, even if several ports are attached at the same site.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Network

open scoped BigOperators Classical

variable {D : ℕ} {P : Type*} {I : Type} [Fintype I] {free : P → ℕ} {join : I → ℕ}

/-- Attach a network with ports `I` to the corresponding ports in an exterior
network. Every join gets its own shared cable, retaining both attachment sites. -/
def sew (O : Network D (P ⊕ I) (Sum.elim free join)) (G : Network D I join) :
    Network D P free where
  Site := O.Site ⊕ G.Site
  Edge := I ⊕ (O.Edge ⊕ G.Edge)
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src := Sum.elim (fun i => .inl (O.attach (.inr i))) <|
    Sum.elim (fun e => .inl (O.src e)) (fun e => .inr (G.src e))
  dst := Sum.elim (fun i => .inr (G.attach i)) <|
    Sum.elim (fun e => .inl (O.dst e)) (fun e => .inr (G.dst e))
  width := Sum.elim join (Sum.elim O.width G.width)
  attach p := .inl (O.attach (.inl p))
  position := Sum.elim O.position G.position
  in_ball := by rintro (v | v); exact O.in_ball v; exact G.in_ball v

/-- Combine the free indices of the exterior with the common joined indices. -/
def joinedPorts (x : Ports free) (s : Ports join) : Ports (Sum.elim free join)
  | .inl p => x p
  | .inr i => s i

variable {R : Type*} [CommSemiring R]

/-- Transport each local table to the sewn network by reading a joined port
from the shared cable at the appropriate endpoint. -/
def sewTables (O : Network D (P ⊕ I) (Sum.elim free join)) (G : Network D I join)
    (outer : O.Tables R) (inner : G.Tables R) : (O.sew G).Tables R := by
  intro v a x
  cases v with
  | inl v =>
    apply outer v
    · intro e
      exact a ⟨.inr (.inl e.val), e.property.imp (congrArg Sum.inl) (congrArg Sum.inl)⟩
    · rintro ⟨p | i, hp⟩
      · exact x ⟨p, congrArg Sum.inl hp⟩
      · exact a ⟨.inl i, Or.inl (congrArg Sum.inl hp)⟩
  | inr v =>
    apply inner v
    · intro e
      exact a ⟨.inr (.inr e.val), e.property.imp (congrArg Sum.inr) (congrArg Sum.inr)⟩
    · intro i
      exact a ⟨.inl i.val, Or.inr (congrArg Sum.inr i.property)⟩

private def assignSplit (O : Network D (P ⊕ I) (Sum.elim free join)) (G : Network D I join) :
    (O.sew G).Assignment ≃ Ports join × (O.Assignment × G.Assignment) :=
  (Equiv.sumPiEquivProdPi _).trans <| Equiv.prodCongr (Equiv.refl _) (Equiv.sumPiEquivProdPi _)

/-- The contraction of the actual glued network factors into the two
subcontractions conditional on a single assignment to all joined ports. -/
theorem value_sew (O : Network D (P ⊕ I) (Sum.elim free join)) (G : Network D I join)
    (outer : O.Tables R) (inner : G.Tables R) (x : Ports free) :
    (O.sew G).value (O.sewTables G outer inner) x =
      ∑ s : Ports join, O.value outer (joinedPorts x s) * G.value inner s := by
  classical
  let block := fun (z : Ports join × (O.Assignment × G.Assignment)) =>
    (∏ v, O.read outer z.2.1 (joinedPorts x z.1) v) * ∏ v, G.read inner z.2.2 z.1 v
  calc
    _ = ∑ z, block z := by
      apply Fintype.sum_equiv (assignSplit O G) _ _
      intro a
      change (∏ v : O.Site ⊕ G.Site, (O.sew G).read (O.sewTables G outer inner) a x v) = _
      refine (Fintype.prod_sum_type (fun v : O.Site ⊕ G.Site =>
        (O.sew G).read (O.sewTables G outer inner) a x v)).trans ?_
      congr 1
      · apply Finset.prod_congr rfl
        intro v _
        apply congrArg (outer v _)
        funext p
        rcases p with ⟨p | i, h⟩ <;> rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro s _
      rw [Fintype.sum_prod_type]
      simp only [block, Network.value, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]

/-- Substituting a finite sum of profile tensors under arbitrary external
connections is exact on every remaining free input. -/
theorem value_sew_sum {J : Type*} [Fintype J]
    (O : Network D (P ⊕ I) (Sum.elim free join)) (outer : O.Tables R)
    (G : Network D I join) (inner : G.Tables R)
    (profile : J → Network D I join) (table : ∀ j, (profile j).Tables R)
    (hid : ∀ s, G.value inner s = ∑ j, (profile j).value (table j) s)
    (x : Ports free) :
    (O.sew G).value (O.sewTables G outer inner) x =
      ∑ j, (O.sew (profile j)).value (O.sewTables (profile j) outer (table j)) x := by
  classical
  simp only [value_sew, hid, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Cable cost is additive under attachment, including the widths and
distances of the hooks at the matching ports. -/
theorem cost_sew (O : Network D (P ⊕ I) (Sum.elim free join)) (G : Network D I join) :
    (O.sew G).cost = (∑ i, (join i : ℝ) *
      dist (O.position (O.attach (.inr i))) (G.position (G.attach i))) + (O.cost + G.cost) := by
  unfold Network.cost
  change (∑ e : I ⊕ (O.Edge ⊕ G.Edge), _) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  rfl

end Crossing.Network

end BorderVNP
end Computability
end OAI
