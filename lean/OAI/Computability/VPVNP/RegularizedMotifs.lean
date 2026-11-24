import OAI.Computability.VPVNP.SlotOtherEnd
import OAI.Computability.VPVNP.SlotRegularization
import OAI.Computability.VPVNP.SlotSeparation
import OAI.Computability.VPVNP.SlotTranslation
import OAI.Computability.VPVNP.SurvivingSlots

/-!
# The regularized graph of a shrinking step

The graph constructed at the end of Section 7.2 of *VP and VNP differ
over every field* is a lift over the pairs consisting of an old base and a
tag. A motif in its lane-zero section supplies one base identifier for each
surviving type and subdivision. The role-to-role displacement restores the
actual lanes at its ends. The uniform role counts give the common deficit
that the cyclic dummy arcs fill.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.PackingData

open SurvivingSlots

variable {V H Tag L : Type*} {d c : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

/-- Each role incidence at an absolute site corresponds to exactly one
lane-zero motif at its packed base. Reindexing by the role's lane handles
both ends of the edge and either layout. -/
def baseRoleFiberEquiv (role : P.Motif → Site V Tag L)
    (hr : ∀ m g, role (P.translateMotif m g) = translateSite (role m) g)
    (b : V × Tag) (g : L) :
    {z : P.BaseMotif // packedBase (role z.1) = b} ≃ {m : P.Motif // role m = (b.1, b.2, g)} := by
  let e := P.roleLaneEquiv role hr
  have atLane (z : P.BaseMotif) (h : L) :
      role (e.symm (z, h)) = ((role z.1).1, (role z.1).2.1, h) :=
    (P.roleLane_endpoints role role hr hr z h).1
  exact {
    toFun := fun z ↦ ⟨e.symm (z.1, g), (atLane z.1 g).trans
      (congrArg (fun b : V × Tag ↦ (b.1, b.2, g)) z.2)⟩
    invFun := fun m ↦ ⟨(e m.1).1, by
      have h := atLane (e m.1).1 (e m.1).2
      rw [Prod.mk.eta, e.symm_apply_apply] at h
      exact (congrArg packedBase h).symm.trans (congrArg packedBase m.2)⟩
    left_inv := fun z ↦ Subtype.ext (congrArg Prod.fst (e.apply_symm_apply (z.1, g)))
    right_inv := fun m ↦ Subtype.ext (e.injective (by
      rw [e.apply_symm_apply]
      refine Prod.ext ?_ ?_
      · rfl
      change g = (role m.1).2.2
      rw [m.2])) }

/-- The packed base of a role of a lane-zero motif. -/
def roleBase (layout : Bool) (r : PackedRole) (z : P.BaseMotif) : V × Tag :=
  packedBase (P.survivingRole layout r z.1)

theorem survivingRole_translate (layout : Bool) (r : PackedRole) (m : P.Motif) (g : L) :
    P.survivingRole layout r (P.translateMotif m g) =
      translateSite (P.survivingRole layout r m) g := by
  cases r with
  | a => exact P.roleA_translate m g
  | b => exact P.roleB_translate m g
  | d => exact P.roleD_translate layout m g

/-- Fixed displacement of a role edge on a lane-zero ID. -/
def roleDisplacement {T : Type*} (layout : Bool) (src dst : T → PackedRole) {subdiv : T → ℕ}
    (i : Id P.BaseMotif subdiv) : L :=
  (P.survivingRole layout (dst i.1) i.2.1.1).2.2 - (P.survivingRole layout (src i.1) i.2.1.1).2.2

/-- Reindex every actual subdivided role edge by its lane-zero ID and its
absolute source-role lane. The inverse recovers the same motif and
subdivision, including when several supply types use the same two roles. -/
def survivingLaneEquiv (layout : Bool) (subdiv : Fin 4 → ℕ) :
    Id P.Motif subdiv ≃ Id P.BaseMotif subdiv × L := by
  let e (t : Fin 4) := P.roleLaneEquiv (P.survivingRole layout (sourceRole layout t))
    (P.survivingRole_translate layout (sourceRole layout t))
  exact {
    toFun := fun ⟨t, m, i⟩ ↦ (⟨t, (e t m).1, i⟩, (e t m).2)
    invFun := fun ⟨⟨t, z, i⟩, g⟩ ↦ ⟨t, (e t).symm (z, g), i⟩
    left_inv := by rintro ⟨t, m, i⟩; simp
    right_inv := by rintro ⟨⟨t, z, i⟩, g⟩; simp }

/-- The reconstructed actual ID has precisely the source and target sites
of the corresponding lifted arc. -/
theorem survivingLane_endpoints (layout : Bool) (subdiv : Fin 4 → ℕ)
    (z : Id P.BaseMotif subdiv) (g : L) :
    let i := (P.survivingLaneEquiv layout subdiv).symm (z, g)
    let src := endpoint (P.roleBase layout) (sourceRole layout) z
    let dst := endpoint (P.roleBase layout) (targetRole layout) z
    endpoint (P.survivingRole layout) (sourceRole layout) i = (src.1, src.2, g) ∧
      endpoint (P.survivingRole layout) (targetRole layout) i =
        (dst.1, dst.2, g +
          P.roleDisplacement layout (sourceRole layout) (targetRole layout) z) := by
  rcases z with ⟨t, m, i⟩
  exact P.roleLane_endpoints _ _ (P.survivingRole_translate layout (sourceRole layout t))
    (P.survivingRole_translate layout (targetRole layout t)) m g

variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]

/-- Each packed base has the same `dQ` role count among lane-zero motifs. -/
theorem card_roleBase (hc : 2 ≤ c) (layout : Bool) (r : PackedRole) (b : V × Tag) :
    Fintype.card {z : P.BaseMotif // P.roleBase layout r z = b} = d * (3 * (2 ^ c * d) / 4) := by
  unfold roleBase
  rw [Fintype.card_congr (P.baseRoleFiberEquiv (P.survivingRole layout r)
    (P.survivingRole_translate layout r) b 0)]
  cases r with
  | a => exact P.card_roleA hc _
  | b => exact P.card_roleB hc _
  | d => exact P.card_roleD hc layout _

/-- The uniform in- and outdegree before cyclic padding. -/
def survivingDegree (d c : ℕ) (subdiv : Fin 4 → ℕ) : ℕ :=
  d * (3 * (2 ^ c * d) / 4) * ∑ t, subdiv t

variable [Module (ZMod 2) Tag]

/-- A lift of the padded, subdivided surviving graph over the packed bases.
Every genuine ID is numbered in the given order of lane-zero IDs, and the
dummy slots go to the next tag without changing the remaining lane. -/
def regularizedSlotIndexing (hc : 2 ≤ c) (hφ : P.slots.ValidTagOffsets P.tagShift P.offset)
    (layout : Bool) (subdiv : Fin 4 → ℕ) [LinearOrder (Id P.BaseMotif subdiv)]
    {d' J : ℕ} (hd : survivingDegree d c subdiv ≤ d') (tagIndex : Tag ≃ Fin J) (hJ : 1 < J) :
    SlotIndexing (V × Tag) (PaddedId (V × Tag) (Id P.BaseMotif subdiv)
      (d' - survivingDegree d c subdiv)) L d'
      (paddedSource (endpoint (P.roleBase layout) (sourceRole layout)))
      (paddedTarget (endpoint (P.roleBase layout) (targetRole layout)) (cycleTags tagIndex))
      (paddedShift (P.roleDisplacement layout (sourceRole layout) (targetRole layout))) := by
  refine paddedSlotIndexing _ _ _ ?_ ?_ ?_ hd _ (cycleTags_ne tagIndex hJ)
  · intro i
    exact (P.survivingSlot_bases_ne hφ layout
      (subdiv := subdiv) ⟨i.1, i.2.1.1, i.2.2⟩).symm
  · exact card_endpoint _ _ subdiv (P.card_roleBase hc layout)
  · exact card_endpoint _ _ subdiv (P.card_roleBase hc layout)

end Compression.PackingData

end VPVNP
end Computability
end OAI
