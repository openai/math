import OAI.Computability.VPVNP.ShrinkMotifGraph
import OAI.Computability.VPVNP.SurvivingSlots

/-!
# Placing the six parties in the two shrinking layouts

In the first layout C and M move to A, and N moves to D. In the second
layout C and N move to B, and M moves to D. Each absorbed edge has one
owner, while the endpoints of the other four edges agree with the roles of
the surviving slots.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

open SurvivingSlots

namespace ShrinkMotif

/-- Site role of A, B, C, D, M and N in each layout. -/
def partyRole (layout : Bool) : Fin 6 → PackedRole
  | 0 => .a
  | 1 => .b
  | 2 => if layout then .b else .a
  | 3 => .d
  | 4 => if layout then .d else .a
  | 5 => if layout then .b else .d

/-- Owner of the edge of this type from the absorbed group. -/
def internalRole (layout : Bool) (t : Fin 4) : PackedRole :=
  partyRole layout (supply.src (!layout,t))

theorem role_src_survives (l : Bool) (t : Fin 4) :
    partyRole l (supply.src (l,t)) = sourceRole l t :=
  (by decide : ∀ l t, partyRole l (supply.src (l,t)) = sourceRole l t) l t

theorem role_dst_survives (l : Bool) (t : Fin 4) :
    partyRole l (supply.dst (l,t)) = targetRole l t :=
  (by decide : ∀ l t, partyRole l (supply.dst (l,t)) = targetRole l t) l t

theorem role_src_absorbed (l : Bool) (t : Fin 4) :
    partyRole l (supply.src (!l,t)) = internalRole l t := rfl

theorem role_dst_absorbed (l : Bool) (t : Fin 4) :
    partyRole l (supply.dst (!l,t)) = internalRole l t :=
  (by decide : ∀ l t, partyRole l (supply.dst (!l,t)) = internalRole l t) l t

variable {M V k : Type*} [Fintype M] [Fintype V] [DecidableEq V] [CommMonoid k]

/-- All six-party factors resident at a site, with its equality proof available
when reading the factor's local arguments. -/
def partyProduct (site : M → Fin 6 → V) (v : V)
    (factor : ∀ m j, v = site m j → k) : k :=
  ∏ m, ∏ j, if h : v = site m j then factor m j h else 1

/-- Placing the factors at their resident sites preserves the full product. -/
theorem prod_partyProduct (site : M → Fin 6 → V) (factor : ∀ v m j, v = site m j → k) :
    (∏ v, partyProduct site v (factor v)) = ∏ m, ∏ j, factor (site m j) m j rfl := by
  unfold partyProduct
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro m _
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  exact Fintype.prod_dite_eq' _ _

end ShrinkMotif

/-- Site coordinates used in the new lifted graph, with the tag in its base. -/
def packedSiteEquiv {V Tag L : Type*} : Site V Tag L ≃ (V × Tag) × L :=
  (Equiv.prodAssoc V Tag L).symm

namespace PackingData

variable {V H Tag L : Type*} {d c : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

/-- Placement of each whole old position on the new lifted graph. -/
def shrinkPlace (l : Bool) (u : Position V H Tag L c) : (V × Tag) × L :=
  packedSiteEquiv (P.placement l u)

/-- The six map matrices are assigned to three packed positions. -/
def shrinkPartySite (l : Bool) (m : P.Motif) (j : Fin 6) : (V × Tag) × L :=
  packedSiteEquiv (P.survivingRole l (ShrinkMotif.partyRole l j) m)

/-- Each absorbed supply edge is summed at the common site of its endpoints. -/
def shrinkInternalOwner (l : Bool) (e : P.Motif × Fin 4) : (V × Tag) × L :=
  packedSiteEquiv (P.survivingRole l (ShrinkMotif.internalRole l e.2) e.1)

theorem shrinkPartySite_C (l : Bool) (m : P.Motif) :
    P.shrinkPartySite l m 2 = P.shrinkPlace l (P.C m) := by
  cases l <;> simp [shrinkPartySite, shrinkPlace, ShrinkMotif.partyRole, survivingRole, roleMap]

end PackingData
end Compression

end VPVNP
end Computability
end OAI
