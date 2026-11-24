import OAI.Computability.VPVNP.SlotOtherEnd
import OAI.Computability.VPVNP.SlotSeparation
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Incidences of the surviving slots in a shrinking step

Section 7.2 of *VP and VNP differ over every field* splits each surviving
supply edge of type `t` into the same number of slots at every motif.
Each of the packed roles A, B, D occurs equally often at every site.
Counting by type gives the same incoming and outgoing degree at every site.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.SurvivingSlots

/-- The three packed positions of one motif, with D denoting the placed D*. -/
inductive PackedRole where
  | a | b | d
  deriving DecidableEq

/-- Apply one of the three role maps of the chosen layout to a motif. -/
def roleMap {M V : Type*} (A B D : M → V) : PackedRole → M → V
  | .a => A
  | .b => B
  | .d => D

/-- Orient the surviving wires in the order of their party names. Layout
`false` retains BC, BN, CN, DM and layout `true` retains AC, AM, CM, DN. -/
def sourceRole (layout : Bool) : Fin 4 → PackedRole
  | 0 | 1 => if layout then .a else .b
  | 2 => if layout then .b else .a
  | 3 => .d

/-- Destination roles after identifying ACM and DN in the first layout,
or BCN and DM in the second layout. -/
def targetRole (layout : Bool) : Fin 4 → PackedRole
  | 0 | 3 => if layout then .b else .a
  | 1 | 2 => .d

theorem sourceRole_ne_targetRole (layout : Bool) (e : Fin 4) :
    sourceRole layout e ≠ targetRole layout e :=
  (by decide : ∀ l : Bool, ∀ t : Fin 4, sourceRole l t ≠ targetRole l t) layout e

/-- The type, original CD arc (motif), and index of a parallel slot. -/
abbrev Id (M : Type*) {T : Type*} (subdiv : T → ℕ) := Σ t, M × Fin (subdiv t)

variable {R M V T : Type*}

/-- The source or target of a surviving slot, determined by the role at
that end of its supply type. -/
def endpoint (role : R → M → V) (pick : T → R) {subdiv : T → ℕ} (i : Id M subdiv) : V :=
  role (pick i.1) i.2.1

/-- Counting the incidences at a vertex can be done separately for each type,
then independently for the motif and the subdivision index. -/
def endpointFiberEquiv (role : R → M → V) (pick : T → R) (subdiv : T → ℕ) (v : V) :
    {i : Id M subdiv // endpoint role pick i = v} ≃
      Σ t, {m : M // role (pick t) m = v} × Fin (subdiv t) where
  toFun i := ⟨i.1.1, ⟨i.1.2.1, i.2⟩, i.1.2.2⟩
  invFun i := ⟨⟨i.1, i.2.1.1, i.2.2⟩, i.2.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The uniform degree formula applies to either orientation. Here `r` is
the common number of occurrences of each role at any site. -/
theorem card_endpoint [Fintype M] [Fintype T] [DecidableEq V]
    (role : R → M → V) (pick : T → R) (subdiv : T → ℕ) {r : ℕ}
    (hrole : ∀ k v, Fintype.card {m : M // role k m = v} = r) (v : V) :
    Fintype.card {i : Id M subdiv // endpoint role pick i = v} = r * ∑ t, subdiv t := by
  rw [Fintype.card_congr (endpointFiberEquiv role pick subdiv v)]
  simp [Fintype.card_prod, hrole, Finset.mul_sum]

/-- Distinct roles give distinct endpoints, including after projection to the
base when the three projected roles are pairwise distinct. -/
theorem endpoint_ne (role : R → M → V) (src dst : T → R)
    (hrole : ∀ m, Function.Injective (fun k ↦ role k m))
    (hdiff : ∀ t, src t ≠ dst t) {subdiv : T → ℕ} (i : Id M subdiv) :
    endpoint role src i ≠ endpoint role dst i :=
  fun h ↦ hdiff i.1 (hrole i.2.1 h)

/-- The three pairwise inequalities of Appendix C imply role injectivity. -/
theorem injective_roleMap (A B D : M → V) (m : M)
    (h : A m ≠ B m ∧ A m ≠ D m ∧ B m ≠ D m) :
    Function.Injective (fun k ↦ roleMap A B D k m) := by
  intro k l he
  cases k <;> cases l <;> simp_all [roleMap, ne_comm]

end Compression.SurvivingSlots

namespace Compression.PackingData

open SurvivingSlots

variable {V H Tag L : Type*} {d c : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

/-- The three role maps of the actual packed layout. -/
def survivingRole (layout : Bool) : PackedRole → P.Motif → Site V Tag L :=
  roleMap P.roleA P.roleB (P.roleD layout)

/-- Each surviving slot has distinct packed bases for its source and target,
including parallel slots of the same supply type. -/
theorem survivingSlot_bases_ne [Module (ZMod 2) Tag]
    (hφ : P.slots.ValidTagOffsets P.tagShift P.offset)
    (layout : Bool) {subdiv : Fin 4 → ℕ} (i : Id P.Motif subdiv) :
    packedBase (endpoint (P.survivingRole layout) (sourceRole layout) i) ≠
    packedBase (endpoint (P.survivingRole layout) (targetRole layout) i) := by
  apply endpoint_ne (fun k m ↦ packedBase (P.survivingRole layout k m)) _ _ _
    (sourceRole_ne_targetRole layout)
  intro m
  have hm := injective_roleMap (packedBase ∘ P.roleA) (packedBase ∘ P.roleB)
    (packedBase ∘ P.roleD layout) m (P.distinct_roleBases hφ layout m)
  have hmap (k : PackedRole) :
      packedBase (P.survivingRole layout k m) = roleMap (packedBase ∘ P.roleA)
        (packedBase ∘ P.roleB) (packedBase ∘ P.roleD layout) k m := by
    cases k <;> rfl
  simpa only [hmap] using hm

variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]

/-- Before filling the deficit, every packed position has exactly
`d * Q * ∑ t, subdiv t` outgoing and incoming arcs in either layout. -/
theorem survivingSlot_degree (hc : 2 ≤ c) (layout : Bool) (subdiv : Fin 4 → ℕ) (s : Site V Tag L) :
    Fintype.card {i : Id P.Motif subdiv //
      endpoint (P.survivingRole layout) (sourceRole layout) i = s} =
      d * (3 * (2 ^ c * d) / 4) * ∑ t, subdiv t ∧
    Fintype.card {i : Id P.Motif subdiv //
      endpoint (P.survivingRole layout) (targetRole layout) i = s} =
      d * (3 * (2 ^ c * d) / 4) * ∑ t, subdiv t := by
  have hrole (k : PackedRole) (v : Site V Tag L) :
      Fintype.card {m : P.Motif // P.survivingRole layout k m = v} = d * (3 * (2 ^ c * d) / 4) := by
    cases k with
    | a => exact P.card_roleA hc v
    | b => exact P.card_roleB hc v
    | d => exact P.card_roleD hc layout v
  exact ⟨card_endpoint _ _ _ hrole s, card_endpoint _ _ _ hrole s⟩

end Compression.PackingData

end VPVNP
end Computability
end OAI
