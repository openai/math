import OAI.ThreeFlat.Diagonal.TraceBucketRelayExpr
import OAI.ThreeFlat.Diagonal.TraceBucketMasks
import OAI.ThreeFlat.Diagonal.LaneBucketAddresses

namespace OAI
/-! # Mixed-radix offset selection and cursor bits of a physical relay slot -/

namespace ThreeFlat.Diagonal.TraceBucketRelay

open LaneCursor RowLayout TracePhysical

theorem chooseSlot_testBit (d o q : ℕ) :
    chooseSlot d o q = ((maskNat d o).testBit q).toNat := by
  by_cases h0 : o=0
  · simp [chooseSlot,maskNat,h0]
  · by_cases h : o≤d
    · have hd : o<d+1 := by omega
      have he : o=q+1 ↔ o-1=q := by omega
      simp [chooseSlot,maskNat,h0,h,hd,Nat.testBit_two_pow,he]; split_ifs <;> simp_all
    · have hd : ¬o<d+1 := by omega
      simp [chooseSlot,maskNat,h0,h,hd,Nat.testBit_two_pow_sub_one]; split_ifs <;> simp_all
      simp [show ¬q<o-d by omega]

theorem tagOrder_slot (offsets low slots : ℕ) (a : Fin (offsets*(2^low*(slots*3)))) :
    ((tagOrder offsets low slots a).1).val = a.val/(2^low*(slots*3)) := rfl

theorem selected_slot {F : Type*} {p k low offsets slots r d : ℕ} {N : BitNetwork F p}
    (P : RowLayout N (k+1) low offsets slots) (hd : ∀ o : Fin offsets, (P.offset o).val=maskNat d o.val)
    (a : Fin (offsets*(2^low*(slots*3)))) (i : Fin (k+1)) :
    (selected (r:=r) P.mask (tagOrder offsets low slots a).1 i).val =
      chooseSlot d (a.val/(2^low*(slots*3))) (low+i.val) := by
  let o := (tagOrder offsets low slots a).1
  have hv : (selected (r:=r) P.mask o i).val = (P.mask o i).val := by
    simp [selected,finProdFinEquiv]
  rw [hv,RowLayout.mask,splitRow_lane]
  dsimp only [highBits]
  rw [Nat.testBit_shiftRight,hd,chooseSlot_testBit,← tagOrder_slot offsets low slots a]
  change ((if (maskNat d o.val).testBit (low+i.val) then 1 else 0 : Fin 2)).val = _
  cases (maskNat d o.val).testBit (low+i.val) <;> rfl

end ThreeFlat.Diagonal.TraceBucketRelay

end OAI
