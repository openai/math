import OAI.Computability.BorderVNP.CellEmitBoxCounts
import OAI.Computability.BorderVNP.CellCQFMeasured

/-! # Actual charges for binary arithmetic on resolved block sizes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram
open private takeWeights sumBinary from OAI.Computability.BorderVNP.CellEmitBoxCounts

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

private theorem sizeBits_le (i : ℕ) : i.bits.length ≤ i := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

/-- The product routine reads the multiplicity and the length of the one-copy table.
Every intermediate binary field has size linear in that compact block. -/
theorem measured_blockMultiplicity :
    Procedure.Measured (fun b => (blockCode b).length) 9 blockMultiplicity id := by
  unfold blockMultiplicity
  apply Procedure.Measured.comp
  · apply Procedure.Measured.pair
    · exact Procedure.Measured.of_degree _ 9 (by decide) _ _ (by cqf_degree) (H := 1) (by simp)
    · apply Procedure.Measured.comp
      · exact Procedure.Measured.of_degree _ 9 (by decide) _ _ (by cqf_degree) (H := 1) (by simp)
      · apply Procedure.Measured.of_degree _ 9 (by decide) _ _ (by cqf_degree) (H := 1)
        intro b
        simp only [blockCode,id_eq,prodCode,pairBits_length,Nat.one_mul]
        omega
  · apply Procedure.Measured.of_degree _ 9 (by decide) _ _ (by cqf_degree) (H := 1)
    intro b
    have h := (sizeBits_le b.factors.length).trans (list_length_le_code Typed.factor b.factors)
    simp only [blockCode,id_eq,prodCode,pairBits_length,Nat.one_mul,Function.comp_apply]
    omega

/-- The prefix routine reverses a list, drops the suffix, and reverses the result.
Its physical intermediate words are bounded by the original list and binary index. -/
theorem measured_takeWeights :
    Procedure.Measured (fun x => (prodCode Typed.naturals Nat.bits x).length) 9 takeWeights id := by
  let e := prodCode Typed.naturals Nat.bits
  let xs := Procedure.first Typed.naturals Nat.bits
  let i := Procedure.second Typed.naturals Nat.bits
  let n := (Procedure.listLength Nat.bits 0).comp xs
  let left := Procedure.binarySub.comp (n.pair i)
  let rev := Procedure.listReverse Nat.bits 0
  let keep := (Procedure.listDrop Nat.bits).comp (left.pair (rev.comp xs))
  have hx : Procedure.Measured (fun x => (e x).length) 9 xs id :=
    Procedure.Measured.of_degree _ 9 (by decide) _ _ (by cqf_degree) (H := 1) (by simp [e])
  have hi : Procedure.Measured (fun x => (e x).length) 9 i id :=
    Procedure.Measured.of_degree _ 9 (by decide) _ _ (by cqf_degree) (H := 1) (by simp [e])
  have hn : Procedure.Measured (fun x => (e x).length) 9 n id := by
    apply Procedure.Measured.comp _ _ _ hx
    apply Procedure.Measured.of_degree _ 9 (by decide) _ _ (by cqf_degree) (H := 1)
    rintro ⟨l,j⟩
    simp [e,prodCode,pairBits_length,Typed.naturals]
    omega
  have hl : Procedure.Measured (fun x => (e x).length) 9 left id := by
    apply Procedure.Measured.comp _ _ _ (Procedure.Measured.pair _ _ _ hn hi)
    apply Procedure.Measured.of_degree _ 9 (by decide) _ _ (by cqf_degree) (H := 1)
    rintro ⟨l,j⟩
    have := (sizeBits_le l.length).trans (list_length_le_code Nat.bits l)
    simp only [e,prodCode,pairBits_length,Typed.naturals,id_eq,Function.comp_apply,Nat.one_mul]
    omega
  have hr : Procedure.Measured (fun x => (e x).length) 9 (rev.comp xs) id := by
    apply Procedure.Measured.comp _ _ _ hx
    apply Procedure.Measured.of_degree _ 9 (by decide) _ _ (by cqf_degree) (H := 1)
    rintro ⟨l,j⟩
    simp only [e,prodCode,pairBits_length,Typed.naturals,id_eq,Nat.one_mul]
    omega
  have hk : Procedure.Measured (fun x => (e x).length) 9 keep id := by
    apply Procedure.Measured.comp _ _ _ (Procedure.Measured.pair _ _ _ hl hr)
    apply Procedure.Measured.of_degree _ 9 (by decide) _ _ (by cqf_degree) (H := 2)
    rintro ⟨l,j⟩
    have := (sizeBits_le (l.length-j)).trans ((Nat.sub_le _ _).trans (list_length_le_code Nat.bits l))
    simp only [e,prodCode,pairBits_length,Typed.naturals,id_eq,Function.comp_apply,listCode_length_rev]
    omega
  unfold takeWeights
  rw [Procedure.Measured.congrFun]
  apply Procedure.Measured.comp _ _ _ hk
  apply Procedure.Measured.of_degree _ 9 (by decide) _ _ (by cqf_degree) (H := 1)
  rintro ⟨l,j⟩
  have h := listCode_length_drop_le Nat.bits (l.length-j) l.reverse
  rw [listCode_length_rev] at h
  simp only [e,prodCode,pairBits_length,Typed.naturals,id_eq,Function.comp_apply,Nat.one_mul]
  omega

/-- The binary subtotal fold already has a ninth-degree clock in the physical input list. -/
theorem measured_sumBinary :
    Procedure.Measured (fun l => (Typed.naturals l).length) 9 sumBinary id :=
  Procedure.Measured.of_degree _ 9 (by decide) _ _ (by cqf_degree) (H := 1) (by simp)

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
