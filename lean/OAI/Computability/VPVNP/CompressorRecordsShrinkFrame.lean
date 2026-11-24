import OAI.Computability.VPVNP.CompressorRecordsBundleInputs

/-!
# Retaining the old incidence and placement directories across shrink passes

Both directories precede the temporary width and ordering arrays. A frame
theorem below the new arena therefore retains their typed readbacks even
when the following pass starts with arbitrary contents in its own region.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open BurstRAM Compression

variable {w a l : ℕ}

namespace IncidenceDirectory

/-- The number of actual port slots, counting every base vertex, lane, and slot in the state. -/
abbrev slotCount (X : State a l) := Fintype.card X.Base * 2^l * 2^a

theorem basePort_lt (X : State a l) (e : X.Base × Fin (2^a)) : (basePort (w := w) X e).val < slotCount X := by
  rw [basePort_number, Fin.val_ofNat]
  exact ((Nat.mod_le ..).trans_lt (baseOrder X e).isLt).trans_le
    (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos l)))

theorem actualPort_lt (X : State a l) (e : (X.Base × BitWord l) × Fin (2^a)) :
    (actualPort (w := w) X e).val < slotCount X := by
  rw [actualPort_number,Fin.val_ofNat]; exact (Nat.mod_le ..).trans_lt (actualOrder X e).isLt

theorem Represents.retain {T : IncidenceDirectory w} {X : State a l} {m m' : Memory w}
    (old : T.Represents X m) {limit : ℕ} (before : ∀ c, (T.column c).val+slotCount X ≤ limit)
    (frame : ∀ addr < limit, m' addr = m addr) : T.Represents X m' := by
  have atBase (c : Fin 6) (e : X.Base × Fin (2^a)) :
      m' (T.column c + basePort X e).val = m (T.column c + basePort X e).val := by
    apply frame; rw [Fin.val_add]; exact ((Nat.mod_le ..).trans_lt
      (Nat.add_lt_add_left (basePort_lt X e) _)).trans_le (before c)
  have atActual (c : Fin 6) (e : (X.Base × BitWord l) × Fin (2^a)) :
      m' (T.column c + actualPort X e).val = m (T.column c + actualPort X e).val := by
    apply frame; rw [Fin.val_add]; exact ((Nat.mod_le ..).trans_lt
      (Nat.add_lt_add_left (actualPort_lt X e) _)).trans_le (before c)
  exact ⟨fun e ↦ (atBase 0 e).trans (old.baseOut e), fun e ↦ (atBase 1 e).trans (old.baseIn e),
    fun e ↦ (atBase 2 e).trans (old.shift e),fun e ↦ (atActual 3 e).trans (old.actualOut e),
    fun e ↦ (atActual 4 e).trans (old.actualIn e),fun e ↦ (atActual 5 e).trans (old.width e)⟩

end IncidenceDirectory

namespace ShrinkRAM

variable {V : Type} {g n : ℕ} {G : LiftedSlots V (2^a) (BitWord (packingLaneBits a g))}
variable {order : V ≃ Fin n} {p : Fin 14 → Word w} {layout : Bool} {m m' : Memory w}

theorem PlacementColumns.retain (old : PlacementColumns G order p layout m) {limit : ℕ}
    (before : ∀ t : Fin 4, (p (t.natAdd 10)).val+PositionCount n a g ≤ limit)
    (frame : ∀ addr < limit, m' addr = m addr) : PlacementColumns G order p layout m' := by
  constructor
  intro x P i
  have hsite : i.val < PositionCount n a g := by
    change (Shrink.oldNumber order x) % (2^w) < _
    rw [← Shrink.oldIndex_val]; exact (Nat.mod_le ..).trans_lt (Fin.isLt _)
  have keep (t : Fin 4) : m' (outAddr p t i) = m (outAddr p t i) := by
    apply frame
    rw [outAddr,Fin.val_add]
    exact ((Nat.mod_le ..).trans_lt (Nat.add_lt_add_left hsite _)).trans_le (before t)
  rw [keep 0,keep 1,keep 2,keep 3]; exact old.atSite x

end ShrinkRAM

end CompressorRecords

end VPVNP
end Computability
end OAI
