import OAI.Computability.BorderVNP.CubeISAOwnedVertexEmit
import OAI.Computability.BorderVNP.CubeISAOwnedPacketRank
import OAI.Computability.BorderVNP.CubeISAOwnedPacketCount

/-! # The packed directory after each owned packet trial

A successful row trial appends exactly one half-cube at the current cursor.
Failed digit trials leave both the cursor and the directory alone. The
resulting initial segment preserves every word below the output bank.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedVertex

open Cube Cube.Physical Cube.Physical.Owned Cube.Physical.VertexIndex

variable {n d blocks : ℕ}

/-- Bank address of the actual packet at its globally stable ordinal. -/
def bankAt (base stride : ℕ) (p : Packet n d blocks) := base + packetIndex p * stride

/-- Optional local trial, also defined past the end of the finite counter for
the natural prefix recursion. -/
def packetAtNat (i : Fin (n+1)) (pair : Symbols d) (k : ℕ) : Option (Packet n d blocks) :=
  if hk : k < packetTrials n d blocks then packetTrial i pair ⟨k,hk⟩ else none

/-- Append one packet using the original selector bank and the directory
memory accumulated from earlier packets. -/
def appendPacket (i : Fin (n+1)) (high : Bool) (base stride width : ℕ) (initial : ℕ → ℕ)
    (p : Packet n d blocks) (z : ℕ × (ℕ → ℕ)) : ℕ × (ℕ → ℕ) :=
  let bank := bankAt base stride p
  let selector := (SelectorRead.decoded initial bank width).val
  (z.1+3*2^n, image z.1 bank selector (2^i.val) (ownerBit i p.1.2 high).toNat z.2 (2^n))

/-- Cursor and physical shared memory after the first `k` local row trials. -/
def rowImage (i : Fin (n+1)) (pair : Symbols d) (high : Bool) (base stride width out : ℕ)
    (initial : ℕ → ℕ) : ℕ → ℕ × (ℕ → ℕ)
  | 0 => (out,initial)
  | k+1 =>
    let z := rowImage i pair high base stride width out initial k
    match packetAtNat (blocks := blocks) i pair k with
    | some p => appendPacket i high base stride width initial p z
    | none => z

/-- An owned row's cursor advances monotonically, and the input bank below
the output interval retains all its words. -/
theorem rowImage_frame (i : Fin (n+1)) (pair : Symbols d) (high : Bool) (base stride width out : ℕ)
    (initial : ℕ → ℕ) (k : ℕ) :
    let z := rowImage (blocks := blocks) i pair high base stride width out initial k
    out ≤ z.1 ∧ ∀ addr < out, z.2 addr = initial addr := by
  induction k with
  | zero => exact ⟨le_rfl,fun _ _ => rfl⟩
  | succ k ih =>
    dsimp only at ih ⊢
    rw [rowImage]
    cases h : packetAtNat (blocks := blocks) i pair k with
    | none => exact ih
    | some p =>
      refine ⟨Nat.le_add_right_of_le ih.1, fun a ha => ?_⟩
      exact (image_outside _ _ _ _ _ _ _ a (.inl (ha.trans_le ih.1))).trans (ih.2 a ha)

/-- Addresses past the current append cursor retain the original word. -/
theorem rowImage_above (i : Fin (n+1)) (pair : Symbols d) (high : Bool) (base stride width out : ℕ)
    (initial : ℕ → ℕ) (k : ℕ) :
    let z := rowImage (blocks := blocks) i pair high base stride width out initial k
    ∀ addr, z.1 ≤ addr → z.2 addr = initial addr := by
  induction k with
  | zero => exact fun _ _ => rfl
  | succ k ih =>
    dsimp only at ih ⊢
    rw [rowImage]
    cases h : packetAtNat (blocks := blocks) i pair k with
    | none => exact ih
    | some p =>
      intro a ha
      exact (image_outside _ _ _ _ _ _ _ a (.inr ha)).trans (ih a ((Nat.le_add_right ..).trans ha))

/-- Once a packet is selected its row order, orientation and global bank address
agree with the arithmetic callback inputs at that counter. -/
theorem selected_fields (i : Fin (n+1)) (pair : Symbols d)
    (t : Fin (packetTrials n d blocks)) (h : packetTrialValid t) :
    let p := (packetRowEquiv i pair ⟨t,h⟩).val
    packetAtNat i pair t.val = some p ∧ p.1.1 i = pair ∧
    p.1.2.toNat = t.val/blocks%2 ∧
    trialPacketIndex d ((d*d)^i.val) blocks pair.val.1.val pair.val.2.val t.val = packetIndex p := by
  refine ⟨by simp [packetAtNat,packetTrial,t.isLt,h],(packetRowEquiv i pair ⟨t,h⟩).property,?_,
    trialPacketIndex_eq i pair ⟨t,h⟩⟩
  change (packetDigits n d blocks t).1.2.toNat = _
  rw [(packetDigits_values t).2.1]
  have hr := Nat.mod_lt (t.val / blocks) (by decide : 0 < 2)
  by_cases he : t.val/blocks%2 = 1
  · simp [he]
  · simp [he]; omega

/-- Selectors in any unchanged prefix have the same validity test and decoded rank. -/
theorem selector_read_congr {x y : ℕ → ℕ} {base width count : ℕ}
    (agree : ∀ j < width, x (base+j) = y (base+j)) :
    SelectorRead.decoded x base width = SelectorRead.decoded y base width ∧
    (SelectorRead.Valid x base width count ↔ SelectorRead.Valid y base width count) := by
  have val : SelectorRead.decoded x base width = SelectorRead.decoded y base width := by
    unfold SelectorRead.decoded
    apply congrArg
    funext j
    rw [agree j.val j.isLt]
  refine ⟨val,?_⟩
  unfold SelectorRead.Valid
  rw [val]
  exact and_congr_left' (forall_congr' fun j => imp_congr_right fun hj => by rw [agree j hj])

end RoutingISA.OwnedVertex

end BorderVNP
end Computability
end OAI
