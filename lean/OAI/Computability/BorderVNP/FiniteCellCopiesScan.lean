import OAI.Computability.BorderVNP.FiniteCellCopies

/-! # A unique joint field subtotal for every repeated site box

The prefix of the physical bank contains the original wires of every copy.
The suffix contains one binary word per scalar for the entire bottom bundle.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldDirectory.Copies

open Crossing CellSparse VPVNP.RAMSerialization
open scoped BigOperators Classical
open private idFacts from OAI.Computability.BorderVNP.FiniteCellCounts

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable {F : Type*} [Fintype F]

/-- Decode the suffix of the physical bit bank at its subtotal addresses. -/
def claimBits (w : ℕ) (c : Fin (Fintype.card F) → Fin w → Bool) (j : ℕ) : Bool :=
  if hj : j < w*Fintype.card F then
    let vi := finProdFinEquiv.symm (⟨j,hj⟩ : Fin (w*Fintype.card F))
    c vi.2 vi.1
  else false

private theorem bank_claim {copies w : ℕ} (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits)
    (c : Fin (Fintype.card F) → Fin w → Bool) (v : Fin (Fintype.card F)) (i : Fin w) :
    bank N a x (claimBits w c) (claimAddress N copies w v i) = c v i := by
  simp only [bank,claimAddress,Nat.not_lt_of_ge (Nat.le_add_right ..),dite_false,Nat.add_sub_cancel_left,
    claimBits,(finProdFinEquiv (i,v)).isLt,dite_true,Fin.eta,Equiv.symm_apply_apply]

private theorem word_claim {copies w : ℕ} (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits)
    (c : Fin (Fintype.card F) → Fin w → Bool) (v : Fin (Fintype.card F)) :
    word (bank N a x (claimBits w c)) (List.ofFn (claimAddress N copies w v)) = ((wordBits w).symm (c v)).val := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < w
  · rw [word_digit _ _ _ (by simpa using hi)]
    simp only [List.getElem_ofFn,bank_claim]
    exact (congrFun ((wordBits w).apply_symm_apply (c v)) ⟨i,hi⟩).symm.trans (VPVNP.LiveHeader.testBit_wordBits _ _).symm
  · have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : w ≤ i)
    have hleft := word_bound (bank N a x (claimBits w c)) (List.ofFn (claimAddress N copies w v))
    rw [List.length_ofFn] at hleft
    rw [Nat.testBit_lt_two_pow (hleft.trans_le hpow),Nat.testBit_lt_two_pow (((wordBits w).symm (c v)).isLt.trans_le hpow)]

/-- A valid report contains the actual total across all copies, for every field element. -/
theorem counts_iff {copies : ℕ} (sites : List N.Site) (table : N.Tables F) (w : ℕ)
    (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits) (c : Fin (Fintype.card F) → Fin w → Bool) :
    countsValid (bank N a x (claimBits w c)) (directory N sites table copies w).reportedCounts
      ((ids N sites table a x).map fun z => (false,some z)) ↔
      ∀ j, (ids N sites table a x).count j.val = ((wordBits w).symm (c j)).val := by
  simp only [countsValid,(idFacts _).1,directory,List.length_ofFn]
  constructor
  · rintro ⟨_,h⟩ j
    have hj := h (Fin.cast (List.length_ofFn ..).symm j)
    simpa only [Fin.getElem_fin,List.getElem_ofFn,Fin.val_cast,word_claim] using hj
  · intro h
    refine ⟨?_,?_⟩
    · intro z hz
      obtain ⟨v,_,rfl⟩ := List.mem_map.mp hz
      exact Fin.isLt _
    · rintro ⟨v,hv⟩
      let j : Fin (List.ofFn fun i : Fin (Fintype.card F) => List.ofFn (claimAddress N copies w i)).length := ⟨v,hv⟩
      have hj := h (Fin.cast (List.length_ofFn ..) j)
      simpa only [j,Fin.cast_mk,Fin.getElem_fin,List.getElem_ofFn,word_claim] using hj

/-- The single joint report is uniquely forced, even when the visits select zero
entries or when the bundle is empty. -/
theorem unique_claims {copies : ℕ} (sites : List N.Site) (table : N.Tables F) (w : ℕ)
    (fits : copies * sites.length < 2^w) (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits) :
    ∃! c : Fin (Fintype.card F) → Fin w → Bool,
      countsValid (bank N a x (claimBits w c)) (directory N sites table copies w).reportedCounts
        ((ids N sites table a x).map fun z => (false,some z)) := by
  let num (j : Fin (Fintype.card F)) : Fin (2^w) := ⟨(ids N sites table a x).count j.val,
    (List.count_le_length ..).trans_lt (by rwa [ids_length])⟩
  refine ⟨fun j => wordBits w (num j), (counts_iff ..).mpr (fun j => by simp [num]), ?_⟩
  intro c hc
  funext j
  apply (wordBits w).symm.injective
  apply Fin.ext
  simpa [num] using ((counts_iff ..).mp hc j).symm

/-- The field elements used by the physical subtotal scanner, indexed by their literal positions. -/
noncomputable def scalar (sites : List N.Site) (table : N.Tables F) (copies w : ℕ) :
    Fin (directory N sites table copies w).reportedCounts.length → F :=
  fun j => (Fintype.equivFin F).symm (Fin.cast (by simp [directory]) j)

variable [Field F]

/-- Apply the sparse directory validator and the concrete stack power scanner once
to the joint report for the whole bundle. -/
noncomputable def scan {copies : ℕ} (sites : List N.Site) (table : N.Tables F) (w : ℕ)
    (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits) (c : Fin (Fintype.card F) → Fin w → Bool) : F :=
  let B := directory N sites table copies w
  let b := bank N a x (claimBits w c)
  let counts := fun i : Fin B.reportedCounts.length => B.reportedCounts[i].map b
  (B.weight b : F) * FieldStack.productPaths (FieldPowers.program (scalar N sites table copies w))
    FieldPowers.factor (fun _ => 1) (1+∑ i, (2*(counts i).length+2)) (.visit (Fin.last _)) counts

/-- At an arbitrary tuple, the scanner returns the full product precisely at the
passing report, and zero elsewhere. -/
theorem scan_claims {copies : ℕ} (sites : List N.Site) (table : N.Tables F) (w : ℕ)
    (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits) (c : Fin (Fintype.card F) → Fin w → Bool) :
    scan N sites table w a x c =
      if (∀ j, (ids N sites table a x).count j.val = ((wordBits w).symm (c j)).val) then
        ∏ i : Fin copies, (sites.map (N.read table (a i) (x i))).prod else 0 := by
  unfold scan
  rw [FieldPowers.cell_weight,observations]
  let B := directory N sites table copies w
  let b := bank N a x (claimBits w c)
  have hbox : ∀ r ∈ B.records, r.Valid B.boxes b := by simp [B,directory,Record.Valid]
  change (if (∀ r ∈ B.records, r.Valid B.boxes b) ∧ countsValid b B.reportedCounts _ then _ else 0) = _
  by_cases hc : ∀ j, (ids N sites table a x).count j.val = ((wordBits w).symm (c j)).val
  · rw [ite_eq_left ⟨hbox,(counts_iff ..).mpr hc⟩,ite_eq_left hc,(idFacts _).1,(idFacts _).2,← entries_prod]
    simp only [Bool.false_eq_true,ite_false,one_mul,ids,List.map_map]
    have he (z : F) : FieldPowers.entry (scalar N sites table copies w) (Fintype.equivFin F z).val = z := by
      have hz : (Fintype.equivFin F z).val < (directory N sites table copies w).reportedCounts.length := by
        simpa only [directory,List.length_ofFn] using (Fintype.equivFin F z).isLt
      rw [FieldPowers.entry,dite_eq_left hz,scalar]
      apply (Fintype.equivFin F).injective
      rw [Equiv.apply_symm_apply]
      exact Fin.ext rfl
    simp [Function.comp_def,he]
  · rw [ite_eq_right (fun h => ((counts_iff ..).mp h.2 |> hc)),ite_eq_right hc]

/-- Logarithmically many bits per scalar suffice for the unique joint report.
The bank uses one stride per copy and a single collection of count words. -/
theorem sum_scan {copies : ℕ} (sites : List N.Site) (table : N.Tables F)
    (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits) :
    let w := Nat.clog 2 (copies*sites.length+1)
    (∑ c, scan N sites table w a x c) = ∏ i : Fin copies, (sites.map (N.read table (a i) (x i))).prod := by
  intro w
  obtain ⟨c₀,h₀,unique⟩ := unique_claims N sites table w (Nat.lt_of_succ_le (Nat.le_pow_clog (by decide) _)) a x
  let good (c : Fin (Fintype.card F) → Fin w → Bool) := ∀ j, (ids N sites table a x).count j.val = ((wordBits w).symm (c j)).val
  have eqc c : good c ↔ c = c₀ := ⟨fun h => unique c ((counts_iff ..).mpr h),fun h => h ▸ (counts_iff ..).mp h₀⟩
  have eqv c : scan N sites table w a x c = if c = c₀ then ∏ i : Fin copies, (sites.map (N.read table (a i) (x i))).prod else 0 := by
    simpa only [← eqc] using scan_claims N sites table w a x c
  simp [eqv]

end FieldDirectory.Copies

end BorderVNP
end Computability
end OAI
