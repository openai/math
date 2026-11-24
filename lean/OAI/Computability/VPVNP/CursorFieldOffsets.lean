import OAI.Computability.VPVNP.CursorRouting
import OAI.Computability.VPVNP.RAMSortAddressBounds

/-!
# Contiguous field offsets on a cursor arc

The arc reserves one eight-word field for each successor mask class, followed
by one sorting block for each layer in phase order. The two choices of arc at
each cursor use the same layout. Its inverse recovers the system and in-field
index of every bit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorRouting

open RAMLayout RAMSort

variable {D H w : ℕ}

/-- Length of the bit vector on either outgoing arc. -/
def ramPayloadWidth (D H w : ℕ) : ℕ :=
  D * (8 * w) + layerCount D * blockBits H w

theorem ramPayloadWidth_eq_sum (D H w : ℕ) :
    ramPayloadWidth D H w = ∑ s : RAMSystem D, ramFieldBits H w s :=
  (ramArcWidth D H w).symm

/-- Number all bits in the arc payload, allowing empty fields and zero width. -/
def ramFieldOffset (D H w : ℕ) :
    ((s : RAMSystem D) × Fin (ramFieldBits H w s)) ≃ Fin (ramPayloadWidth D H w) :=
  let succ := (Equiv.sigmaEquivProd (Fin D) (Fin (8 * w))).trans finProdFinEquiv
  let sort := (Equiv.sigmaEquivProd (Layer D) (Fin (blockBits H w))).trans
    (((layerEquiv D).prodCongr (Equiv.refl _)).trans finProdFinEquiv)
  (Equiv.sumSigmaDistrib (fun s : RAMSystem D => Fin (ramFieldBits H w s))).trans
    ((succ.sumCongr sort).trans finSumFinEquiv)

@[simp] theorem ramFieldOffset_successor (k : Fin D) (j : Fin (8 * w)) :
    (ramFieldOffset D H w ⟨.inl k, j⟩).val = k.val * (8 * w) + j.val := by
  change j.val + 8 * w * k.val = _
  ring

@[simp] theorem ramFieldOffset_sort (l : Layer D) (j : Fin (blockBits H w)) :
    (ramFieldOffset D H w ⟨.inr l, j⟩).val =
      D * (8 * w) + l.ordinal.val * blockBits H w + j.val := by
  change D * (8 * w) + (j.val + blockBits H w * l.ordinal.val) = _
  ring

/-- Flatten the separate field functions to a single vector of arc bits. -/
def ramPayloadEquiv (D H w : ℕ) :
    ((s : RAMSystem D) → Fin (ramFieldBits H w s) → Bool) ≃ (Fin (ramPayloadWidth D H w) → Bool) :=
  (Equiv.piCurry (fun (s : RAMSystem D) (_ : Fin (ramFieldBits H w s)) => Bool)).symm.trans
    ((ramFieldOffset D H w).arrowCongr (Equiv.refl Bool))

@[simp] theorem ramPayloadEquiv_offset
    (payload : (s : RAMSystem D) → Fin (ramFieldBits H w s) → Bool)
    (s : RAMSystem D) (j : Fin (ramFieldBits H w s)) :
    ramPayloadEquiv D H w payload (ramFieldOffset D H w ⟨s, j⟩) = payload s j := by
  change Sigma.uncurry payload ((ramFieldOffset D H w).symm (ramFieldOffset D H w ⟨s, j⟩)) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Straight-line word arithmetic for a bit address. The sorting case computes
the triangular prefix from the phase and step counters. -/
def ramFieldAddress (D H w : ℕ) (s : RAMSystem D) (j : Fin (ramFieldBits H w s)) : IndexExpr :=
  let successorBits := IndexExpr.mul (.arg 8) (.arg w)
  match s with
  | .inl k => .add (.mul (.arg k.val) successorBits) (.arg j.val)
  | .inr l =>
    let phase := IndexExpr.arg l.phase
    let ordinal := IndexExpr.add (.div (.mul phase (.add phase (.arg 1))) (.arg 2)) (.arg l.step)
    let block := IndexExpr.mul (.mul (.mul (.arg 4) (.arg H)) (.arg 5)) (.arg w)
    .add (.add (.mul (.arg D) successorBits) (.mul ordinal block)) (.arg j.val)

theorem ramFieldAddress_eval (s : RAMSystem D) (j : Fin (ramFieldBits H w s)) :
    (ramFieldAddress D H w s j).eval = (ramFieldOffset D H w ⟨s, j⟩).val := by
  cases s with
  | inl k => exact (ramFieldOffset_successor (H := H) k j).symm
  | inr l =>
    rw [ramFieldOffset_sort (H := H) (w := w) l j]
    simp only [ramFieldAddress, IndexExpr.eval, Layer.ordinal, layerCount,
      Nat.choose_two_right, Nat.add_sub_cancel, blockBits]
    rw [Nat.mul_comm l.phase (l.phase + 1)]

/-- The address calculation uses at most thirteen arithmetic instructions
regardless of the number of successor classes or sorting layers. -/
theorem ramFieldAddress_work (s : RAMSystem D) (j : Fin (ramFieldBits H w s)) :
    (ramFieldAddress D H w s j).work ≤ 13 := by
  cases s <;> simp [ramFieldAddress, IndexExpr.work]

/-- Every temporary register fits below or at the total payload width. This
includes the product in the triangular prefix before division by two. -/
theorem ramFieldAddress_peak_le (s : RAMSystem D) (j : Fin (ramFieldBits H w s)) :
    (ramFieldAddress D H w s j).peak ≤ ramPayloadWidth D H w := by
  have haddr := (ramFieldOffset D H w ⟨s, j⟩).isLt
  cases s with
  | inl k =>
    have hj : j.val < 8 * w := j.isLt
    have hk := k.isLt
    have hwidth := Nat.le_mul_of_pos_left (8 * w) (show 0 < D by omega)
    have hD := Nat.le_mul_of_pos_right D (show 0 < 8 * w by omega)
    rw [ramFieldOffset_successor (H := H) k j] at haddr
    simp only [ramFieldAddress, IndexExpr.peak, IndexExpr.eval, max_le_iff]
    unfold ramPayloadWidth at *
    repeat' constructor <;> omega
  | inr l =>
    have hj : j.val < blockBits H w := j.isLt
    have hpos : 0 < 4 * H * 5 * w := hj.trans_le' (Nat.zero_le _)
    have hw : 0 < w := Nat.pos_of_mul_pos_left hpos
    have hH : 0 < H := by
      by_contra!
      simp_all
    have h20 := Nat.le_mul_of_pos_right (4 * H * 5) hw
    have hmin : 2 ≤ blockBits H w := by unfold blockBits; omega
    have hord : l.phase * (l.phase + 1) / 2 + l.step < layerCount D := by
      simpa [Layer.ordinal, layerCount, Nat.choose_two_right, Nat.mul_comm l.phase] using
        l.ordinal.isLt
    have hp := l.phase_lt
    have hsucc := Nat.le_mul_of_pos_left (8 * w) (show 0 < D by omega)
    have hD := Nat.le_mul_of_pos_right D (show 0 < 8 * w by omega)
    have hblock := Nat.le_mul_of_pos_left (blockBits H w) (show 0 < layerCount D by omega)
    have hlayers := Nat.mul_le_mul_left (layerCount D) hmin
    rw [ramFieldOffset_sort (H := H) (w := w) l j] at haddr
    simp only [Layer.ordinal, layerCount, Nat.choose_two_right, Nat.add_sub_cancel,
      Nat.mul_comm (l.phase + 1) l.phase] at haddr
    change D * (8 * w) + (l.phase * (l.phase + 1) / 2 + l.step) * blockBits H w + j.val <
      ramPayloadWidth D H w at haddr
    simp only [ramFieldAddress, IndexExpr.peak, IndexExpr.eval, max_le_iff]
    unfold ramPayloadWidth at *
    unfold blockBits at *
    repeat' constructor <;> omega

/-- With a register large enough to hold the payload length, modular word
evaluation gives the exact bit address. -/
theorem ramFieldAddress_evalWord {bits : ℕ} (h : ramPayloadWidth D H w < 2 ^ bits)
    (s : RAMSystem D) (j : Fin (ramFieldBits H w s)) :
    ((ramFieldAddress D H w s j).evalWord bits).val = (ramFieldOffset D H w ⟨s, j⟩).val :=
  ((ramFieldAddress D H w s j).evalWord_eq ((ramFieldAddress_peak_le s j).trans_lt h)).trans
    (ramFieldAddress_eval s j)

end CursorRouting

end VPVNP
end Computability
end OAI
