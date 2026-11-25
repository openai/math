import OAI.Computability.MultitapeWeakETH.IncidenceProgram
import OAI.Computability.VPVNP.CompressorDescriptorSpace
import OAI.Computability.VPVNP.CompressorRecordsShrinkFrame

/-! # Initial packed incidence memory for a formula graph -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork.InitialIncidence

open VPVNP Compression CompressorRecords DescriptorSpace BurstRAM CursorRAM
open scoped Classical
noncomputable section

/-- The reserved size of each of the six column arrays, even when its active
entries are indexed only by base ports. -/
def rows (a g r : ℕ) := (2*(g+(r+2))-2+2)*2^g*2^a

theorem slot_count (a g r : ℕ) : IncidenceDirectory.slotCount (inputState a g r) = rows a g r := by
  change Fintype.card (Fin _) * 2^g * 2^a = _
  rw [Fintype.card_fin]
  rfl

/-- Initialize the six arrays and retain the caller's words elsewhere. -/
def install {w : ℕ} (a g r start : ℕ) (m : Memory w) : Memory w := fun x =>
  let N := rows a g r
  if start ≤ x ∧ x < start+6*N then
    CursorRAM.encode w (column a g r (Fin.ofNat 6 ((x-start)/N)) ((x-start)%N))
  else m x

theorem install_outside {w : ℕ} (a g r start : ℕ) (m : Memory w) (x : ℕ)
    (outside : x < start ∨ start+6*rows a g r ≤ x) : install a g r start m x = m x := by
  simp only [install,ite_eq_right_iff]
  omega

private theorem cell {a g r start w : ℕ} (m : Memory w) (room : start+6*rows a g r ≤ 2^w)
    (c : Fin 6) {i : ℕ} (hi : i < rows a g r) :
    install a g r start m ((CursorRAM.encode w (start+c.val*rows a g r)+CursorRAM.encode w i).val) =
      CursorRAM.encode w (column a g r c i) := by
  let N := rows a g r
  have high : start+c.val*N+i < start+6*N := Nat.add_assoc .. ▸ Nat.add_lt_add_left (packed_lt c.isLt hi) start
  change start+6*N ≤ 2^w at room
  have addr : (CursorRAM.encode w (start+c.val*N)+CursorRAM.encode w i).val=start+c.val*N+i := by
    rw [Fin.val_add,Fin.val_ofNat,Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : start+c.val*N < 2^w),
      Nat.mod_eq_of_lt (by omega : i < 2^w),Nat.mod_eq_of_lt (high.trans_le room)]
  change install a g r start m ((CursorRAM.encode w (start+c.val*N)+CursorRAM.encode w i).val) = _
  rw [addr]
  unfold install
  change (if start ≤ start+c.val*N+i ∧ start+c.val*N+i < start+6*N then _ else _) = _
  rw [ite_eq_left ⟨by omega,high⟩]
  change CursorRAM.encode w (column a g r (Fin.ofNat 6 ((start+c.val*N+i-start)/N)) ((start+c.val*N+i-start)%N)) = _
  rw [Nat.add_assoc,Nat.add_sub_cancel_left,Nat.mul_add_mod_of_lt hi,Nat.mul_comm c.val N,
    Nat.mul_add_div (by omega),Nat.div_eq_of_lt hi,Nat.add_zero]
  rw [show Fin.ofNat 6 c.val=c from Fin.ext (Nat.mod_eq_of_lt c.isLt)]

/-- All six physical columns represent the actual slot bijection, its
inverse, the displacement, and the payload width at every port. -/
theorem represents {a g r w : ℕ} (L : Layout) (level : ℕ) (m : Memory w)
    (room : incidenceStart L level+6*rows a g r ≤ 2^w) :
    (packedIncidence L w level (IncidenceDirectory.slotCount (inputState a g r))).Represents
      (inputState a g r) (install a g r (incidenceStart L level) m) := by
  rw [slot_count]
  let d := 2*(g+(r+2))-2+2
  have hb (i : Fin d) (p : Fin (2^a)) : i.val*2^a+p.val < rows a g r :=
    (packed_lt i.isLt p.isLt).trans_le (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right d (Nat.two_pow_pos g)))
  have ha (i : Fin d) (x : BitWord g) (p : Fin (2^a)) :
      (i.val*2^g+(bitWordFinEquiv g x).val)*2^a+p.val < rows a g r :=
    packed_lt (packed_lt i.isLt (bitWordFinEquiv g x).isLt) p.isLt
  constructor
  · rintro ⟨i,p⟩
    exact (cell m room 0 (hb i p)).trans (congrArg (CursorRAM.encode w) (base_columns (g:=g) (r:=r) i p).1)
  · rintro ⟨i,p⟩
    exact (cell m room 1 (hb i p)).trans (congrArg (CursorRAM.encode w) (base_columns (g:=g) (r:=r) i p).2.1)
  · rintro ⟨i,p⟩
    exact (cell m room 2 (hb i p)).trans (congrArg (CursorRAM.encode w) (base_columns (g:=g) (r:=r) i p).2.2)
  · rintro ⟨⟨i,x⟩,p⟩
    exact (cell m room 3 (ha i x p)).trans (congrArg (CursorRAM.encode w) (actual_columns (r:=r) i x p).1)
  · rintro ⟨⟨i,x⟩,p⟩
    exact (cell m room 4 (ha i x p)).trans (congrArg (CursorRAM.encode w) (actual_columns (r:=r) i x p).2.1)
  · rintro ⟨⟨i,x⟩,p⟩
    exact (cell m room 5 (ha i x p)).trans (congrArg (CursorRAM.encode w) (actual_columns (r:=r) i x p).2.2)

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork.InitialIncidence
