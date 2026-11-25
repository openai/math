import OAI.Hierarchy.DescentPacketFactorShape
import OAI.Hierarchy.DescentResetOperandBookInvoice
import OAI.Hierarchy.DescentPlacedInvoiceVolume

namespace OAI
/-! # Cost of pulling one lane of operand packets from the root directory -/
namespace Hierarchy.DescentPacketPullInvoiceVolume

open DescentSIMDLookup DescentOperandFamilyBook DescentPlacedInvoiceVolume


theorem one (L : DescentOperandRootPull.Layout) (h T : ℕ)
    (ha : 0 < L.beforeLanes) (hm : 0 < L.afterLanes) (hx : 0 < L.blocks)
    (limA : L.beforeLanes ≤ h) (limB : L.afterLanes * L.blocks ≤ h)
    (source : L.width * L.beforeLanes ≤ h / 2) (dest : (L.width * L.blocks) * L.afterLanes ≤ h / 2)
    (original : L.actors * chunks (L.groups * L.blocks) L.beforeLanes ≤ T)
    (position : L.actors * chunks L.groups L.afterLanes ≤ T)
    (shelf : (h + 1)^3 * 2^(h/2) ≤ T) (actors : L.actors ≤ T)
    (rows : L.receivers * chunks L.groups L.afterLanes ≤ T)
    (joint : (L.width + L.width) * L.afterLanes ≤ h / 2) :
    L.invoice ≤ factor L.fields L.blocks * (T+1) := by
  have proj := projection 1 L.actors L.groups L.blocks L.width L.beforeLanes L.afterLanes h T
    ha hm hx limA limB source dest original position shelf
  have scan : DescentResetCandidatePair.scanBill 1 (L.actors*chunks (L.groups*L.blocks) L.beforeLanes) 7 ≤
      500*(T+1) := by unfold DescentResetCandidatePair.scanBill; omega
  have span₁ := DescentDyadicSpan.span_le L.actors
  have span₂ := DescentDyadicSpan.span_le (L.receivers*chunks L.groups L.afterLanes)
  have key : dictionaryCharge (DescentResetStemKeyReindex.size L.actors L.receivers L.groups L.afterLanes) ≤
      1000*(T+1) := by unfold dictionaryCharge DescentResetStemKeyReindex.size; omega
  have exp : 2^((L.width + L.width) * L.afterLanes) ≤ T :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) joint).trans
      ((Nat.le_mul_of_pos_left _ (by positivity : 0 < (h+1)^3)).trans shelf)
  have lut : words L.fields 1 L.width L.afterLanes ≤ (1 + L.fields)*(2*T) := by
    simpa only [words, unit, Nat.mul_one] using
      Nat.mul_le_mul_left (1 + L.fields) (Nat.mul_le_mul_left 2 exp)
  have book : dictionaryCharge (words L.fields 1 L.width L.afterLanes) ≤
      1000*(L.fields+1)*(T+1) := by
    unfold dictionaryCharge
    calc
      _ ≤ 4+10*((1+L.fields)*(2*T))+7*(15*((1+L.fields)*(2*T)+1)) := by gcongr
      _ ≤ _ := by ring_nf; omega
  unfold DescentOperandRootPull.Layout.invoice
  apply (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 4096 proj) scan) key) book).trans
  unfold factor
  ring_nf
  omega

end Hierarchy.DescentPacketPullInvoiceVolume

end OAI
