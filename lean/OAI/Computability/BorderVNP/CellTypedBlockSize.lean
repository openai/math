import OAI.Computability.BorderVNP.CellBoxResolutionMeter
import OAI.Computability.BorderVNP.CellLocalFactorLength

/-! # Bit length of the resolved one-copy block directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram

/-- Field widths of resolved references are inherited from the original public records
and the actual referenced private tables. A missing private table has no factors. -/
theorem resolved_fields (D : Directory) {p U : ℕ} (h : RawFields D p U) (b : BoxBlock)
    (hb : b ∈ D.blocks) : b.base ≤ U ∧ b.copies ≤ U ∧ b.stride ≤ U ∧
      ∀ f ∈ b.factors, FactorFields f U := by
  obtain ⟨r,hr,he⟩ := List.mem_filterMap.mp hb
  cases r with
  | zero | equal | profile => contradiction
  | box id base c stride =>
    change some (⟨base,c,stride,D.boxes.getD id []⟩ : BoxBlock) = some b at he
    obtain rfl := Option.some.inj he
    obtain ⟨_,_,hbase,hc,hs⟩ := h.records (.box id base c stride) hr
    refine ⟨hbase,hc,hs,?_⟩
    intro f hf
    by_cases hi : id < D.boxes.length
    · exact (h.boxes D.boxes[id] (List.getElem_mem hi)).2 f
        (by simpa only [List.getD,List.getElem?_eq_getElem hi,Option.getD_some] using hf)
    · simp only [List.getD,List.getElem?_eq_none (Nat.le_of_not_gt hi),Option.getD_none,List.not_mem_nil] at hf

private def factorMass (fs : List Factor) := (fs.map fun f => 10000*f.staticMass).sum

private theorem factor_list_length (fs : List Factor) {U : ℕ}
    (h : ∀ f ∈ fs, FactorFields f U) :
    (listCode Typed.factor fs).length ≤ 2*(fs.length+factorMass fs)*(U.size+1)+1 := by
  induction fs with
  | nil => simp [listCode,factorMass]
  | cons f fs ih =>
    have hx := typed_factor_length_of_mass f (h f List.mem_cons_self)
    have hi := ih (fun x hx => h x (.tail _ hx))
    simp only [factorMass,List.map_cons,List.sum_cons,List.length_cons,listCode_length_cons] at hi ⊢
    nlinarith only [hx,hi,Nat.zero_le (f.staticMass*(U.size+1)),Nat.zero_le U.size]

private theorem block_entry_length (b : BoxBlock) {U : ℕ}
    (h : b.base ≤ U ∧ b.copies ≤ U ∧ b.stride ≤ U ∧ ∀ f ∈ b.factors, FactorFields f U) :
    2*(blockCode b).length+2 ≤
      8*(4+b.factors.length+factorMass b.factors)*(U.size+1) := by
  have hl := factor_list_length b.factors h.2.2.2
  have hb := Nat.size_le_size h.1
  have hc := Nat.size_le_size h.2.1
  have hs := Nat.size_le_size h.2.2.1
  simp only [blockCode,prodCode,pairBits_length,Nat.size_eq_bits_len]
  nlinarith only [hl,hb,hc,hs,Nat.zero_le (b.factors.length*(U.size+1)),
    Nat.zero_le (factorMass b.factors*(U.size+1)),Nat.zero_le U.size]

/-- Resolving repeated private references increases stored data only according to the
actual one-copy sweep mass and the widths of the original scalar fields. -/
theorem resolved_length_le (D : Directory) {p U : ℕ} (h : RawFields D p U) :
    (listCode blockCode D.blocks).length ≤ 8*D.boxMass*(U.size+1) := by
  have gen (bs : List BoxBlock) (hh : ∀ b ∈ bs, b ∈ D.blocks) :
      (listCode blockCode bs).length ≤
        8*((bs.map fun b => 4+b.factors.length+factorMass b.factors).sum+1)*(U.size+1) := by
    induction bs with
    | nil => simp [listCode]; omega
    | cons b bs ih =>
      have hi := ih (fun z hz => hh z (.tail _ hz))
      have hx := block_entry_length b (resolved_fields D h b (hh b List.mem_cons_self))
      simp only [listCode_length_cons,List.map_cons,List.sum_cons]
      nlinarith only [hi,hx]
  exact gen D.blocks (fun _ hx => hx)

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
