import OAI.ThreeFlat.Diagonal.CompressorRefreshGraph

namespace OAI
/-! # Source and target annotations of the padded lifted slot graph -/

namespace ThreeFlat.Diagonal.CompressorRefresh

open Computability.VPVNP.Compression

variable {B L : Type*} {a b : ℕ}

/-- Outgoing and incoming slot lists in the union, on every lane. -/
def unionLabels (B L : Type*) (a b : ℕ) :
    (((B × Fin a) × L) ⊕ ((B × Fin b) × L)) ≃ (B × Fin (a+b)) × L :=
  (Equiv.sumProdDistrib _ _ _).symm.trans ((slotCases B a b).symm.prodCongr (Equiv.refl L))

theorem unionLabels_left (p : B × Fin a) (g : L) :
    unionLabels B L a b (.inl (p,g)) = ((slotCases B a b).symm (.inl p),g) := rfl

theorem unionLabels_right (p : B × Fin b) (g : L) :
    unionLabels B L a b (.inr (p,g)) = ((slotCases B a b).symm (.inr p),g) := rfl

@[simp] theorem unionLabels_left_base (p : (B × Fin a) × L) :
    (unionLabels B L a b (.inl p)).1.1 = p.1.1 := rfl

@[simp] theorem unionLabels_left_lane (p : (B × Fin a) × L) :
    (unionLabels B L a b (.inl p)).2 = p.2 := rfl

/-- Padding preserves the destination, including its lane, of every old slot. -/
theorem union_actual_left [AddCommGroup L] (A : LiftedSlots B a L) (C : LiftedSlots B b L)
    (p : (B × Fin a) × L) :
    (union A C).actualTarget (unionLabels B L a b (.inl p)) =
      unionLabels B L a b (.inl (A.actualTarget p)) := by
  obtain ⟨p,g⟩ := p
  simp [unionLabels_left, LiftedSlots.actualTarget,union,unionTarget_left]

end ThreeFlat.Diagonal.CompressorRefresh

end OAI
