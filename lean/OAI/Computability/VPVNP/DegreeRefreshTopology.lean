import OAI.Computability.VPVNP.SlotGraph
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Prod
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.Group.Fin.Basic

/-!
# The regular topology after a degree refresh

Section 7.3 of *VP and VNP differ over every field* promotes the port
coordinate to a base label. Each port has a single external arc, one
internal arc per expander slot, and cyclic padding arcs. The external arc
retains the old shift of the remaining lane. Internal and padding arcs
stay within a block.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

variable {V H L : Type*} {D dH d₀ : ℕ}

/-- Relabeling the port component of the old lane leaves a bijection of positions. -/
def refreshPositions (port : H ≃ Fin D) : V × (H × L) ≃ (V × Fin D) × L :=
  ((Equiv.refl V).prodCongr (port.prodCongr (Equiv.refl L))).trans (Equiv.prodAssoc _ _ _).symm

@[simp] theorem refreshPositions_apply (port : H ≃ Fin D) (v : V) (j : H) (g : L) :
    refreshPositions port (v,j,g) = ((v,port j),g) := rfl

/-- Group old outgoing slots by their source block and slot, keeping the old
port as the last index within each bundle. The same indexing applies to
incoming slots. -/
def bundleCoordinates (port : H ≃ Fin D) :
    ((V × Fin D) × (H × L)) ≃ ((V × L) × Fin D) × Fin D where
  toFun p := (((p.1.1, p.2.2), p.1.2), port p.2.1)
  invFun p := ((p.1.1.1, p.1.2), (port.symm p.2, p.1.1.2))
  left_inv _ := by simp
  right_inv _ := by simp

/-- A source block and slot determine the destination block and incoming slot. -/
def bundleTarget [AddCommGroup L] (G : LiftedSlots V D (H × L)) :
    Equiv.Perm ((V × L) × Fin D) :=
  (LiftedSlots.mk G.base (fun p => (G.displacement p).2)).actualGraph.target

@[simp] theorem bundleTarget_apply [AddCommGroup L] (G : LiftedSlots V D (H × L))
    (x : V) (g : L) (i : Fin D) :
    bundleTarget G ((x,g),i) =
      (((G.base.target (x,i)).1, g + (G.displacement (x,i)).2), (G.base.target (x,i)).2) := rfl

/-- The port component of the displacement bijects each source bundle's
ordered segments with the old ports at the destination. -/
def bundlePort [AddCommGroup H] (G : LiftedSlots V D (H × L)) (port : H ≃ Fin D)
    (b : (V × L) × Fin D) : Equiv.Perm (Fin D) :=
  port.symm.trans ((Equiv.addRight (G.displacement (b.1.1,b.2)).1).trans port)

@[simp] theorem bundlePort_apply [AddCommGroup H] (G : LiftedSlots V D (H × L))
    (port : H ≃ Fin D) (b : (V × L) × Fin D) (j : Fin D) :
    bundlePort G port b j = port (port.symm j + (G.displacement (b.1.1,b.2)).1) := rfl

/-- Express the original matching in bundle coordinates. The destination
block and slot are independent of the source segment, which is relabeled by
the port translation of the old arc. -/
theorem actualTarget_bundleCoordinates [AddCommGroup H] [AddCommGroup L]
    (G : LiftedSlots V D (H × L)) (port : H ≃ Fin D) (b : (V × L) × Fin D) (j : Fin D) :
    bundleCoordinates port (G.actualTarget ((bundleCoordinates port).symm (b,j))) =
      (bundleTarget G b, bundlePort G port b j) := rfl

/-- A slot is external, internal, or a copy of the cyclic padding arc. -/
abbrev RefreshSlot (dH d₀ : ℕ) := Fin 1 ⊕ (Fin dH ⊕ Fin (d₀ - (dH + 1)))

/-- Number the three classes of slots in their stated order. -/
def refreshSlots (hd : dH + 1 ≤ d₀) : RefreshSlot dH d₀ ≃ Fin d₀ :=
  ((Equiv.refl (Fin 1)).sumCongr finSumFinEquiv).trans
    (finSumFinEquiv.trans (finCongr (by omega)))

private def refreshTarget (G : SlotGraph V D) (P : SlotGraph (Fin D) dH) :
    Equiv.Perm ((V × Fin D) × RefreshSlot dH d₀) where
  toFun
    | (p, .inl k) => (G.target p, .inl k)
    | ((v,j), .inr (.inl k)) => ((v,(P.target (j,k)).1), .inr (.inl (P.target (j,k)).2))
    | ((v,j), .inr (.inr k)) => ((v,finRotate D j), .inr (.inr k))
  invFun
    | (p, .inl k) => (G.target.symm p, .inl k)
    | ((v,j), .inr (.inl k)) =>
      ((v,(P.target.symm (j,k)).1), .inr (.inl (P.target.symm (j,k)).2))
    | ((v,j), .inr (.inr k)) => ((v,(finRotate D).symm j), .inr (.inr k))
  left_inv p := by
    rcases p with ⟨⟨v,j⟩, k | k | k⟩ <;> simp [-finRotate_apply, -finRotate_symm_apply]
  right_inv p := by
    rcases p with ⟨⟨v,j⟩, k | k | k⟩ <;> simp [-finRotate_apply, -finRotate_symm_apply]

private theorem rotate_ne_self (hD : 1 < D) (j : Fin D) : finRotate D j ≠ j := by
  have : NeZero D := ⟨by omega⟩
  rw [finRotate_apply]
  intro h
  have hz : (1 : Fin D) = 0 := add_left_cancel (a := j) (show j + 1 = j + 0 by simpa using h)
  have := congrArg Fin.val hz
  simp [Nat.mod_eq_of_lt hD] at this

/-- The new base slot graph has degree exactly `d₀` in both directions
and each arc joins distinct base vertices. -/
def refreshBase (G : SlotGraph V D) (P : SlotGraph (Fin D) dH) (hD : 1 < D)
    (hd : dH + 1 ≤ d₀) : SlotGraph (V × Fin D) d₀ where
  target :=
    let e := (Equiv.refl (V × Fin D)).prodCongr (refreshSlots hd)
    e.symm.trans ((refreshTarget G P).trans e)
  ends_ne := by
    rintro ⟨⟨v,j⟩, i⟩
    obtain ⟨k | k | k, rfl⟩ := (refreshSlots hd).surjective i
    · simpa [refreshTarget] using fun he : G.target (v,j) = (v,j) =>
        G.ends_ne (v,j) (congrArg Prod.fst he)
    · simpa [refreshTarget] using P.ends_ne (j,k)
    · simpa [refreshTarget] using rotate_ne_self hD j

/-- The sole external wire preserves the old shift on the remaining lane.
All internal wires and cyclic padding wires have zero displacement. -/
def degreeRefresh [Zero L] (G : LiftedSlots V D (H × L)) (P : SlotGraph (Fin D) dH)
    (hD : 1 < D) (hd : dH + 1 ≤ d₀) : LiftedSlots (V × Fin D) d₀ L where
  base := refreshBase G.base P hD hd
  displacement := fun p => match (refreshSlots hd).symm p.2 with
    | .inl _ => (G.displacement p.1).2
    | .inr _ => 0

variable [AddCommGroup L] (G : LiftedSlots V D (H × L)) (P : SlotGraph (Fin D) dH)
  (hD : 1 < D) (hd : dH + 1 ≤ d₀)

-- Apply the three slot-specific simp rules before the generic `LiftedSlots.actualGraph_target`.
/-- The old outgoing slot is the source port of the bundled external wire;
the old incoming slot is its destination port. -/
@[simp high] theorem degreeRefresh_external (p : V × Fin D) (g : L) :
    (degreeRefresh G P hD hd).actualGraph.target ((p,g), refreshSlots hd (.inl 0)) =
      ((G.base.target p, g + (G.displacement p).2), refreshSlots hd (.inl 0)) := by
  simp [LiftedSlots.actualGraph_target, degreeRefresh, refreshBase, refreshTarget]

/-- Expander slots connect ports of the same block with the expander's
specified outgoing and incoming slot numbers. -/
@[simp high] theorem degreeRefresh_internal (v : V) (j : Fin D) (g : L) (k : Fin dH) :
    (degreeRefresh G P hD hd).actualGraph.target
      (((v,j),g), refreshSlots hd (.inr (.inl k))) =
      (((v,(P.target (j,k)).1),g), refreshSlots hd (.inr (.inl (P.target (j,k)).2))) := by
  simp [LiftedSlots.actualGraph_target, degreeRefresh, refreshBase, refreshTarget]

/-- Each padding slot is a separate copy of the edge to the cyclic successor. -/
@[simp high] theorem degreeRefresh_padding (v : V) (j : Fin D) (g : L) (k : Fin (d₀ - (dH + 1))) :
    (degreeRefresh G P hD hd).actualGraph.target
      (((v,j),g), refreshSlots hd (.inr (.inr k))) =
      (((v,finRotate D j),g), refreshSlots hd (.inr (.inr k))) := by
  simp [LiftedSlots.actualGraph_target, degreeRefresh, refreshBase, refreshTarget]

end Compression

end VPVNP
end Computability
end OAI
