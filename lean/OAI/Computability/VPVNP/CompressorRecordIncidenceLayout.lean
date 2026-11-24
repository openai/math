import OAI.Computability.VPVNP.CompressorRecordsCursor

/-!
# Shared incidence columns between compressor levels

The same slot numbering serves cursor, shrink and refresh states. This module records the
three actual columns independently of the three base columns. A packed six-column layout
assigns each cell a distinct address for the entire state, including at every parallel slot.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.IncidenceDirectory

open BurstRAM Compression CursorRAM

variable {w a l : ℕ}

/-- The three actual columns use the common state-relative slot numbering. -/
structure ActualColumns (T : IncidenceDirectory w) (X : State a l) (m : Memory w) : Prop where
  actualOut : ∀ e, m (T.actualOut + actualPort X e).val = actualPort X (X.slots.actualGraph.target e)
  actualIn : ∀ e, m (T.actualIn + actualPort X e).val = actualPort X (X.slots.actualGraph.target.symm e)
  width : ∀ e, m (T.width + actualPort X e).val = encode w (X.width ((e.1.1,e.2),e.1.2))

theorem Represents.actual {T : IncidenceDirectory w} {X : State a l} {m : Memory w}
    (h : T.Represents X m) : T.ActualColumns X m := ⟨h.actualOut,h.actualIn,h.width⟩

/-- Base forward, base inverse, displacement, actual forward, actual inverse and width. -/
def column (T : IncidenceDirectory w) : Fin 6 → Word w :=
  ![T.baseOut, T.baseIn, T.shift, T.actualOut, T.actualIn, T.width]

/-- Canonical base and actual slot orders as finite equivalences. -/
def baseOrder (X : State a l) : X.Base × Fin (2^a) ≃ Fin (Fintype.card X.Base * 2^a) :=
  (X.baseIndex.prodCongr (Equiv.refl _)).trans finProdFinEquiv

/-- Number actual slots in base-vertex, lane, then local-port order, with the local port
varying fastest. -/
def actualOrder (X : State a l) : (X.Base × BitWord l) × Fin (2^a) ≃ Fin (Fintype.card X.Base * 2^l * 2^a) :=
  (((X.baseIndex.prodCongr (bitWordFinEquiv l)).trans finProdFinEquiv).prodCongr (Equiv.refl _)).trans finProdFinEquiv

theorem baseOrder_val (X : State a l) (e : X.Base × Fin (2^a)) :
    (baseOrder X e).val = (X.baseIndex e.1).val * 2^a + e.2.val := by
  change e.2.val + 2^a * (X.baseIndex e.1).val = _
  ring

theorem actualOrder_val (X : State a l) (e : (X.Base × BitWord l) × Fin (2^a)) :
    (actualOrder X e).val = ((X.baseIndex e.1.1).val * 2^l + (bitWordFinEquiv l e.1.2).val) * 2^a + e.2.val := by
  change e.2.val + 2^a * ((bitWordFinEquiv l e.1.2).val + 2^l * (X.baseIndex e.1.1).val) = _
  ring

theorem basePort_number (X : State a l) (e : X.Base × Fin (2^a)) :
    basePort (w := w) X e = encode w (baseOrder X e).val := by rw [baseOrder_val]; rfl

theorem actualPort_number (X : State a l) (e : (X.Base × BitWord l) × Fin (2^a)) :
    actualPort (w := w) X e = encode w (actualOrder X e).val := by rw [actualOrder_val]; rfl

/-- Column addresses are disjoint through the last actual slot, and all slot IDs fit. -/
structure Layout (T : IncidenceDirectory w) (X : State a l) : Prop where
  fit : Fintype.card X.Base * 2^l * 2^a ≤ 2^w
  apart : ∀ (c d : Fin 6) (i j : Word w), i.val < Fintype.card X.Base * 2^l * 2^a →
    j.val < Fintype.card X.Base * 2^l * 2^a → ((T.column c + i).val = (T.column d + j).val ↔ c = d ∧ i = j)

theorem Layout.packed {T : IncidenceDirectory w} (X : State a l) (start : ℕ)
    (room : start + 6*(Fintype.card X.Base * 2^l * 2^a) ≤ 2^w)
    (bases : ∀ c : Fin 6, (T.column c).val = start + c.val * (Fintype.card X.Base * 2^l * 2^a)) :
    T.Layout X := by
  let N := Fintype.card X.Base * 2^l * 2^a
  change start + 6 * N ≤ 2^w at room
  constructor
  · change N ≤ 2^w; omega
  · intro c d i j hi hj
    change i.val < N at hi
    change j.val < N at hj
    have address (k : Fin 6) (u : Word w) (hu : u.val < N) :
        (T.column k + u).val = start + k.val*N + u.val := by
      have hk := Nat.mul_le_mul_right N k.isLt
      rw [Nat.succ_mul] at hk
      rw [Fin.val_add, bases k, Nat.mod_eq_of_lt (by change start + k.val*N + u.val < _; omega)]
    rw [address _ _ hi, address _ _ hj]
    constructor
    · intro h
      have ha : c.val*N + i.val = d.val*N + j.val := by omega
      have hij : i = j := Fin.ext ((Nat.mul_add_mod_of_lt hi).symm.trans
        ((congrArg (· % N) ha).trans (Nat.mul_add_mod_of_lt hj)))
      subst j
      exact ⟨Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega : 0 < N) (Nat.add_right_cancel ha)),rfl⟩
    · rintro ⟨rfl,rfl⟩; rfl

end CompressorRecords.IncidenceDirectory

end VPVNP
end Computability
end OAI
