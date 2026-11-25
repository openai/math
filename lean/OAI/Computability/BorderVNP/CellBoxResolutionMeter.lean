import OAI.Computability.BorderVNP.CellBoxMapMeter
import OAI.Computability.BorderVNP.CellBoxPrimitiveMeter

/-! # Physical clock for compact box reference resolution and prefix sums -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram
open private resolve resolveP blocks_eq from OAI.Computability.BorderVNP.CellEmitBoxes
open private weights oneWeight sumBinary takeWeights from OAI.Computability.BorderVNP.CellEmitBoxCounts

set_option maxRecDepth 35000
set_option maxHeartbeats 5000000

/-- The source directory and its resolved one-copy descriptors are the largest words
handled by the compact reference and prefix computations. -/
def blockSpan (D : Directory) := (Typed.directory D).length + (listCode blockCode D.blocks).length

private theorem refs_le (rs : List Record) :
    (listCode refCode (rs.flatMap refOf)).length ≤ (recordsCode rs).length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    cases r <;> simp only [List.flatMap_cons,refOf,List.nil_append,List.singleton_append,
      listCode_length_cons,recordsCode] at ih ⊢
    all_goals try omega
    simp only [Typed.record,Typed.recordFields,sumCode,List.length_cons]
    change 2*(refCode _).length+2+_ ≤ 2*((refCode _).length+1+1+1)+2+_
    omega

private theorem weight_length (b : BoxBlock) : (b.copies*b.factors.length).bits.length ≤ (blockCode b).length := by
  have h := bits_length_mul b.copies b.factors.length
  have hs : b.factors.length.bits.length ≤ b.factors.length := by
    rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hl := list_length_le_code Typed.factor b.factors
  simp only [blockCode,prodCode,pairBits_length]
  omega

private theorem weights_le (bs : List BoxBlock) :
    (Typed.naturals (bs.map fun b => b.copies*b.factors.length)).length ≤ (listCode blockCode bs).length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have := weight_length b
    simp only [Typed.naturals,List.map_cons,listCode_length_cons] at ih ⊢
    omega

/-- Every actual compact lookup is bounded by degree thirty in the original and resolved
word lengths. This includes repeated references to one private box. -/
theorem measured_getBlocks : Procedure.Measured blockSpan 30 getBlocks id := by
  unfold getBlocks
  rw [Procedure.Measured.congrFun]
  apply Procedure.Measured.comp
  · apply Procedure.Measured.pair
    · exact Procedure.Measured.of_degree _ 30 (by decide) _ _ (by cqf_degree) (H := 1)
        (by simp [blockSpan])
    · exact Procedure.Measured.of_degree _ 30 (by decide) _ _ (by cqf_degree) (H := 1)
        (by simp [blockSpan])
  · apply Procedure.Measured.enlarge (e:=30) (d:=10) _ (by decide)
    apply Procedure.measured_listMapWith (H:=2) (K:=resolveP.bound.eval 1*2^9)
    · intro D
      have h := refs_le D.records
      change (prodCode boxesCode (listCode refCode) (D.boxes,D.records.flatMap refOf)).length+
          (listCode blockCode ((D.records.flatMap refOf).map (resolve D.boxes))).length+1 ≤ _
      rw [blocks_eq]
      simp only [Typed.directory,blockSpan,prodCode,pairBits_length,recordsCode,boxesCode] at h ⊢
      omega
    · intro D b hb
      change b ∈ D.records.flatMap refOf at hb
      have h := code_le_of_mem refCode hb
      have hr := refs_le D.records
      have hlen : (prodCode boxesCode refCode (D.boxes,b)).length+1 ≤ 2*(blockSpan D+1) := by
        simp only [blockSpan,Typed.directory,prodCode,pairBits_length,boxesCode,recordsCode] at hr ⊢
        simp only [refCode,prodCode,pairBits_length] at h hr
        omega
      have hc := resolveP.cost_pow (D.boxes,b) (d:=9) (by cqf_degree)
      exact hc.trans (by simpa only [Nat.mul_pow,Nat.mul_assoc] using
        Nat.mul_le_mul_left (resolveP.bound.eval 1) (Nat.pow_le_pow_left hlen 9))

private theorem measured_oneWeight :
    Procedure.Measured (fun x => (prodCode emptyCode blockCode x).length) 9 oneWeight id := by
  unfold oneWeight
  apply Procedure.Measured.comp
  · exact Procedure.Measured.of_degree _ 9 (by decide) _ _ (by cqf_degree) (H := 1) (by simp)
  · apply Procedure.Measured.reparam measured_blockMultiplicity _ (H:=1)
    intro x
    simp only [prodCode,pairBits_length,id_eq,Nat.one_mul]
    omega

private theorem measured_weights : Procedure.Measured blockSpan 30 weights id := by
  unfold weights
  apply Procedure.Measured.comp
  · apply Procedure.Measured.pair
    · exact Procedure.Measured.of_degree _ 30 (by decide) _ _ (by cqf_degree) (H:=1)
        (by simp [blockSpan])
    · exact measured_getBlocks
  · obtain ⟨K,hK⟩ := measured_oneWeight
    apply Procedure.Measured.enlarge (e:=30) (d:=10) _ (by decide)
    apply Procedure.measured_listMapWith (H:=3) (K:=K*2^9)
    · intro D
      have h := weights_le D.blocks
      change (prodCode emptyCode (listCode blockCode) ((),D.blocks)).length+
          (Typed.naturals (D.blocks.map fun b => b.copies*b.factors.length)).length+1 ≤ _
      simp only [blockSpan,prodCode,pairBits_length,emptyCode,List.length_nil]
      omega
    · intro D b hb
      change b ∈ D.blocks at hb
      have := code_le_of_mem blockCode hb
      have hsize : (prodCode emptyCode blockCode ((),b)).length+1 ≤ 2*(blockSpan D+1) := by
        simp only [blockSpan,prodCode,pairBits_length,emptyCode,List.length_nil]
        omega
      exact ((Procedure.cost_le_meter oneWeight ((),b)).trans (hK ((),b))).trans (by
        simpa only [Nat.mul_pow,Nat.mul_assoc] using Nat.mul_le_mul_left K (Nat.pow_le_pow_left hsize 9))

/-- The actual binary subtotal computation has a uniform operational bound, including
its compact source resolution and the computation of every original multiplicity. -/
theorem measured_getVisitCount : Procedure.Measured blockSpan 30 getVisitCount id := by
  unfold getVisitCount
  apply Procedure.Measured.comp _ _ _ measured_weights
  apply Procedure.Measured.enlarge (d:=9) _ (by decide)
  apply Procedure.Measured.reparam measured_sumBinary _ (H:=1)
  intro D
  have := weights_le D.blocks
  simp only [blockSpan,id_eq,Nat.one_mul]
  omega

/-- Prefix computations are charged on the actual resolved directory and binary index,
even if the requested index is beyond the number of physical descriptors. -/
theorem measured_getBlockStart : Procedure.Measured (fun x => blockSpan x.1 + x.2.bits.length)
    30 getBlockStart id := by
  let s := fun x : Directory × ℕ => blockSpan x.1 + x.2.bits.length
  let d := Procedure.first Typed.directory Nat.bits
  let i := Procedure.second Typed.directory Nat.bits
  let w := weights.comp d
  have hd : Procedure.Measured s 30 d id := Procedure.Measured.of_degree _ _ (by decide)
    _ _ (by cqf_degree) (H:=3) (by intro x; simp only [s,blockSpan,id_eq,prodCode,pairBits_length]; omega)
  have hi : Procedure.Measured s 30 i id := Procedure.Measured.of_degree _ _ (by decide)
    _ _ (by cqf_degree) (H:=3) (by intro x; simp only [s,blockSpan,id_eq,prodCode,pairBits_length]; omega)
  have hw : Procedure.Measured s 30 w id := by
    apply Procedure.Measured.comp _ _ _ hd
    exact Procedure.Measured.reparam measured_weights _ (H:=1) (by simp [s])
  have hk : Procedure.Measured s 30 (takeWeights.comp (w.pair i)) id := by
    apply Procedure.Measured.comp _ _ _ (Procedure.Measured.pair _ _ _ hw hi)
    apply Procedure.Measured.enlarge (d:=9) _ (by decide)
    apply Procedure.Measured.reparam measured_takeWeights _ (H:=3)
    intro x
    have := weights_le x.1.blocks
    simp only [s,blockSpan,prodCode,pairBits_length,id_eq,Function.comp_apply]
    omega
  unfold getBlockStart
  rw [Procedure.Measured.congrFun]
  apply Procedure.Measured.comp _ _ _ hk
  apply Procedure.Measured.enlarge (d:=9) _ (by decide)
  apply Procedure.Measured.reparam measured_sumBinary _ (H:=1)
  intro x
  have h := listCode_length_take_le Nat.bits x.2 (x.1.blocks.map fun b => b.copies*b.factors.length)
  have h' := weights_le x.1.blocks
  simp only [s,blockSpan,id_eq,Function.comp_apply,Nat.one_mul,Typed.naturals] at h' ⊢
  omega

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
