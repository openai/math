import OAI.Computability.BorderVNP.CellRecordEmit
import OAI.Computability.BorderVNP.CellTypedRecordSize
import OAI.Computability.BorderVNP.CellCQFListMapCost
import OAI.Computability.BorderVNP.CellCQFListFlattenCost

/-! # Actual native cost of constructing every public wiring descriptor

The native compiler counts stored boxes once. Its common mapping environment
is this one scalar, so the possibly high-degree profile procedure only sees
one fixed-dictionary record with binary addresses. The degree in the length
of the complete directory is at most ten.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram

/-- The emitted leaf's input consists of one count followed by one actual record. -/
def RowInputs (D : Directory) (H : ℕ) : Prop :=
  ∀ r ∈ D.records, (prodCode Nat.bits Typed.record (D.boxes.length,r)).length ≤ H

/-- A raw per-record field count and the maximum binary integer width control
the small words submitted to the isolated compiler. -/
theorem rowInputs_of_fields (D : Directory) (p : ℕ) {U B : ℕ} (h : RawFields D p U)
    (hrows : ∀ r ∈ D.records, (Packet.record r).length ≤ B) :
    RowInputs D ((64*B+3)*(U.size+1)) := by
  intro r hr
  have := typed_record_length_of_field_count D p h hrows r hr
  have := Nat.size_le_size h.lengths.1
  simp only [prodCode,pairBits_length,Nat.size_eq_bits_len]
  rw [Nat.add_mul]
  omega

/-- The pointwise clock uses the input length for one record separately from
the encoded size of the complete directory. -/
noncomputable def recordScale (D : Directory) (H : ℕ) :=
  (Typed.directory D).length + H + smallGuard.bound.eval H + 4

private theorem directory_lengths (D : Directory) :
    (boxesCode D.boxes).length + (recordsCode D.records).length ≤ (Typed.directory D).length := by
  simp only [Typed.directory,prodCode,pairBits_length,boxesCode,recordsCode]
  omega

private theorem map_envelope (X : ℕ) (hx : 1 ≤ X) :
    X*(X+(4*X)^9+(6*X^2)^2+1) ≤ 300000*X^10 := by
  have h2 := Nat.pow_le_pow_right (show 0<X by omega) (show 2 ≤ 10 by decide)
  have h5 := Nat.pow_le_pow_right (show 0<X by omega) (show 5 ≤ 10 by decide)
  have h1 := Nat.pow_le_pow_right (show 0<X by omega) (show 1 ≤ 10 by decide)
  nlinarith only [h2,h5,h1,Nat.zero_le (X^10)]

/-- Actual runtime of the complete fixed public-record serializer at its real directory
and bounded per-record inputs, with a degree-ten dependence on total metadata length. -/
theorem getRecordGuards_cost : ∃ K : ℕ, ∀ D H, RowInputs D H →
    getRecordGuards.cost D ≤ K*(recordScale D H)^10 := by
  let mapper := Procedure.listMapWith (f := fun n r => CellMacro.Generator.serialized 8 (countedGuard n r))
    (.box 0 0 0 0) [] smallGuard
  let gather := getBoxCount.pair getRecords
  let J := Procedure.listJoinWords.bound.eval 1
  let G := gather.bound.eval 1
  obtain ⟨K,hK⟩ := Procedure.cost_listMapWith Nat.bits Typed.record id (.box 0 0 0 0) []
  refine ⟨300000*K+16*J+G+40, fun D H hrow => ?_⟩
  let X := recordScale D H
  let C := smallGuard.bound.eval H
  let L := H+C
  let data := (D.boxes.length,D.records)
  let frames := D.records.map fun r => CellMacro.Generator.serialized 8 (countedGuard D.boxes.length r)
  have hsize : (Typed.directory D).length + L + 4 = X := by simp [L,C,X,recordScale,Nat.add_assoc]
  have hx : 1 ≤ X := by omega
  have hd := directory_lengths D
  have hbl := list_length_le_code (listCode Typed.factor) D.boxes
  have hrl := list_length_le_code Typed.record D.records
  have hbits : D.boxes.length.bits.length ≤ D.boxes.length := by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr Nat.lt_two_pow_self
  change D.boxes.length ≤ (boxesCode D.boxes).length at hbl
  change D.records.length ≤ (recordsCode D.records).length at hrl
  have hdlen : (prodCode Nat.bits (listCode Typed.record) data).length+1 ≤ 4*X := by
    simp only [data,prodCode,pairBits_length]
    change 2*D.boxes.length.bits.length+(recordsCode D.records).length+1+1 ≤ _
    omega
  have hrows : D.records.length+1 ≤ X := by omega
  have hout (r : Record) (hr : r ∈ D.records) :
      (CellMacro.Generator.serialized 8 (countedGuard D.boxes.length r)).length ≤ L := by
    apply (smallGuard.output_length_le (D.boxes.length,r)).trans
    exact Nat.add_le_add (hrow _ hr) (Procedure.eval_nat_mono _ (hrow _ hr))
  have hcost (r : Record) (hr : r ∈ D.records) : smallGuard.cost (D.boxes.length,r) ≤ C :=
    (smallGuard.cost_le_bound _).trans (Procedure.eval_nat_mono _ (hrow _ hr))
  have hs : Procedure.tabSpan (prodCode Nat.bits (listCode Typed.record)) D.records.length data L ≤ 6*X^2 := by
    unfold Procedure.tabSpan
    have hh : (D.records.length+1)*(L+1) ≤ X*X := Nat.mul_le_mul hrows (by omega)
    have hp : X ≤ X^2 := Nat.le_self_pow (by decide) _
    rw [pow_two] at hp ⊢
    omega
  have hm := hK (f := fun n r => CellMacro.Generator.serialized 8 (countedGuard n r)) smallGuard data (L := L) (C := C) hout hcost
  change mapper.cost data ≤ K*(D.records.length+1)*(C+_+_+1) at hm
  have hm' : mapper.cost data ≤ (300000*K)*X^10 := by
    apply hm.trans
    calc _ ≤ K*X*(X+(4*X)^9+(6*X^2)^2+1) := by gcongr; dsimp [L] at hsize; omega
         _ = K*(X*(X+(4*X)^9+(6*X^2)^2+1)) := Nat.mul_assoc ..
         _ ≤ K*(300000*X^10) := Nat.mul_le_mul_left _ (map_envelope X hx)
         _ = _ := by ring
  have hf := listCode_length_map_bound id (fun r => CellMacro.Generator.serialized 8 (countedGuard D.boxes.length r))
    D.records L hout
  change (listCode id frames).length ≤ D.records.length*(2*L+2)+1 at hf
  have hf' : (listCode id frames).length+1 ≤ 4*X^2 := by
    have hh := Nat.mul_le_mul (show D.records.length ≤ X by omega) (show 2*L+2 ≤ 2*X by omega)
    rw [Nat.mul_left_comm X 2 X,← pow_two] at hh
    have hp := Nat.one_le_pow 2 X hx
    omega
  have hpow (k : ℕ) (hk : k ≤ 10) : X^k ≤ X^10 := Nat.pow_le_pow_right (by omega) hk
  have hj : Procedure.listJoinWords.cost frames ≤ (16*J)*X^10 := by
    apply (Procedure.cost_listJoinWords frames).trans
    calc _ ≤ J*(4*X^2)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hf' 2)
         _ = (16*J)*X^4 := by ring
         _ ≤ _ := Nat.mul_le_mul_left _ (hpow _ (by decide))
  have hg := gather.cost_pow D (d := 4) (by dsimp [gather]; cqf_degree)
  have hg' := hg.trans (Nat.mul_le_mul_left G ((Nat.pow_le_pow_left (show (Typed.directory D).length+1 ≤ X by omega) 4).trans (hpow _ (by decide))))
  have hh := Procedure.cost_comp mapper gather D
  change (mapper.comp gather).cost D ≤ mapper.cost data + (4*(prodCode Nat.bits (listCode Typed.record) data).length+2) + gather.cost D at hh
  have hj' := Procedure.cost_comp Procedure.listJoinWords (mapper.comp gather) D
  change (Procedure.listJoinWords.comp (mapper.comp gather)).cost D ≤ Procedure.listJoinWords.cost frames + (4*(listCode id frames).length+2) + (mapper.comp gather).cost D at hj'
  unfold getRecordGuards
  rw [Procedure.cost_congrFun]
  change (Procedure.listJoinWords.comp (mapper.comp gather)).cost D ≤ (300000*K+16*J+G+40)*X^10
  rw [Nat.add_mul,Nat.add_mul,Nat.add_mul]
  have hp₁ : X ≤ X^10 := by simpa using hpow 1 (by decide)
  have hp₂ := hpow 2 (by decide)
  omega

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
