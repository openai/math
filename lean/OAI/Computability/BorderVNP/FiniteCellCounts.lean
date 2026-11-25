import OAI.Computability.BorderVNP.FiniteCellDirectory
import OAI.Computability.VPVNP.LiveHeaderBits

/-! # Unique finite-field multiplicity reports in a private cell

The bit bank first lists the network lanes and then one fixed-width subtotal per
field element. For any list of local sites and any fixed cable assignment, exactly
one tuple of subtotal words passes the cell checker. Its field-valued scanner
returns the product of all selected site entries.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldDirectory

open Crossing CellSparse VPVNP.RAMSerialization
open scoped Classical BigOperators

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable {F : Type*} [Fintype F]

/-- Numbering of every bit of a subtotal following the last original wire bit. -/
noncomputable def claimAddress (w : ℕ) (v : Fin (Fintype.card F)) (i : Fin w) : ℕ :=
  Fintype.card (Wire N) + (finProdFinEquiv (i,v)).val

/-- A public box record references one copy of the cell's local input tables. -/
noncomputable def directory (sites : List N.Site) (table : N.Tables F) (w : ℕ) : Directory where
  boxes := [sites.map (factor N table)]
  records := [.box 0 0 1 0]
  reportedCounts := List.ofFn fun v : Fin (Fintype.card F) => List.ofFn (claimAddress N w v)

/-- Convert a guessed tuple of subtotal words to their actual bank positions. -/
noncomputable def tail (w : ℕ) (claims : Fin (Fintype.card F) → Fin w → Bool) (j : ℕ) : Bool :=
  if hj : j - Fintype.card (Wire N) < w * Fintype.card F then
    let pair := finProdFinEquiv.symm (⟨j-Fintype.card (Wire N),hj⟩ : Fin (w*Fintype.card F))
    claims pair.2 pair.1
  else false

private theorem bank_claim (w : ℕ) (a : N.Assignment) (x : Ports bits)
    (c : Fin (Fintype.card F) → Fin w → Bool) (v : Fin (Fintype.card F)) (i : Fin w) :
    bank N a x (tail N w c) (claimAddress N w v i) = c v i := by
  have h := (finProdFinEquiv (i,v)).isLt
  simp only [bank,claimAddress,Nat.not_lt_of_ge (Nat.le_add_right ..),dite_false,tail,Nat.add_sub_cancel_left,
    h,dite_true,Fin.eta,Equiv.symm_apply_apply]

/-- The checked subtotal at a named scalar equals the integer encoded by those
physical claim bits, including at the empty word width. -/
theorem word_claim (w : ℕ) (a : N.Assignment) (x : Ports bits)
    (c : Fin (Fintype.card F) → Fin w → Bool) (v : Fin (Fintype.card F)) :
    word (bank N a x (tail N w c)) (List.ofFn (claimAddress N w v)) = ((wordBits w).symm (c v)).val := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < w
  · rw [word_digit _ _ _ (by simpa using hi)]
    simp only [List.getElem_ofFn,bank_claim]
    exact (congrFun ((wordBits w).apply_symm_apply (c v)) ⟨i,hi⟩).symm.trans (VPVNP.LiveHeader.testBit_wordBits _ _).symm
  · have hpow : 2^w ≤ (2:ℕ)^i := Nat.pow_le_pow_right (by decide) (by omega)
    have hleft := word_bound (bank N a x (tail N w c)) (List.ofFn (claimAddress N w v))
    rw [List.length_ofFn] at hleft
    rw [Nat.testBit_lt_two_pow (hleft.trans_le hpow),Nat.testBit_lt_two_pow (((wordBits w).symm (c v)).isLt.trans_le hpow)]

/-- The scalar position selected at each stored site. -/
noncomputable def ids (sites : List N.Site) (table : N.Tables F) (a : N.Assignment) (x : Ports bits) : List ℕ :=
  sites.map fun s => (Fintype.equivFin F (N.read table a x s)).val

private theorem siteObservations (sites : List N.Site) (table : N.Tables F) (a : N.Assignment) (x : Ports bits)
    (extra : ℕ → Bool) (w : ℕ) : (directory N sites table w).observations (bank N a x extra) =
    some ((ids N sites table a x).map fun v => (false,some v)) := by
  have visits : (directory N sites table w).occurrences = sites.map (fun s => (⟨factor N table s,0,0⟩ : Occurrence)) := by
    simp [Directory.occurrences,directory,List.map_map,Function.comp_def,List.range_succ]
  rw [Directory.observations,visits]
  clear visits
  induction sites with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map_cons,List.mapM_cons,observe_factor,Option.bind_some,ih,Option.pure_def,Option.bind_eq_bind,ids] at *

private theorem idFacts (vs : List ℕ) :
    ((vs.map fun v => (false,some v)).filterMap Prod.snd) = vs ∧
    (((vs.map fun v => (false,some v)).map Prod.fst).foldl Bool.xor false) = false := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    constructor
    · change v :: _ = v :: vs
      rw [ih.1]
    · exact ih.2

/-- The literal sparse count checks enforce exactly the true multiplicity in
every numbered field position. -/
theorem countsValid_iff (sites : List N.Site) (table : N.Tables F) (w : ℕ) (a : N.Assignment) (x : Ports bits)
    (c : Fin (Fintype.card F) → Fin w → Bool) :
    countsValid (bank N a x (tail N w c)) (directory N sites table w).reportedCounts
      ((ids N sites table a x).map fun v => (false,some v)) ↔
      ∀ j, (ids N sites table a x).count j.val = ((wordBits w).symm (c j)).val := by
  simp only [countsValid,(idFacts _).1,directory,List.length_ofFn]
  constructor
  · rintro ⟨_, h⟩ j
    have hj := h (Fin.cast (List.length_ofFn ..).symm j)
    simpa only [Fin.getElem_fin,List.getElem_ofFn,Fin.val_cast,word_claim] using hj
  · intro h
    refine ⟨?_, ?_⟩
    · intro z hz
      obtain ⟨s,_,rfl⟩ := List.mem_map.mp hz
      exact Fin.isLt _
    · rintro ⟨v,hv⟩
      let j : Fin (List.ofFn fun i : Fin (Fintype.card F) => List.ofFn (claimAddress N w i)).length := ⟨v,hv⟩
      have hj := h (Fin.cast (List.length_ofFn ..) j)
      simpa only [j,Fin.cast_mk,Fin.getElem_fin,List.getElem_ofFn,word_claim] using hj

/-- If all observations fit, there is exactly one accepted report tuple. -/
theorem unique_claims (sites : List N.Site) (table : N.Tables F) (w : ℕ) (fits : sites.length < 2^w)
    (a : N.Assignment) (x : Ports bits) :
    ∃! c : Fin (Fintype.card F) → Fin w → Bool,
      countsValid (bank N a x (tail N w c)) (directory N sites table w).reportedCounts
        ((ids N sites table a x).map fun v => (false,some v)) := by
  let idList := ids N sites table a x
  let num (j : Fin (Fintype.card F)) : Fin (2^w) := ⟨idList.count j.val,
    (List.count_le_length ..).trans_lt (by simpa [idList,ids] using fits)⟩
  refine ⟨fun j => wordBits w (num j), (countsValid_iff ..).mpr (fun j => by simp [num,idList]), ?_⟩
  intro c hc
  funext j
  apply (wordBits w).symm.injective
  apply Fin.ext
  simpa [num,idList] using ((countsValid_iff ..).mp hc j).symm

/-- Interpret each literal position as its original scalar. -/
noncomputable def scalar (sites : List N.Site) (table : N.Tables F) (w : ℕ) :
    Fin (directory N sites table w).reportedCounts.length → F :=
  fun j => (Fintype.equivFin F).symm (Fin.cast (by simp [directory]) j)

variable [Field F]

/-- With an arbitrary proposed tuple the field-valued private scanner returns
the original local product on the unique passing tuple and zero on the others. -/
theorem scan_claims (sites : List N.Site) (table : N.Tables F) (w : ℕ)
    (a : N.Assignment) (x : Ports bits) (c : Fin (Fintype.card F) → Fin w → Bool) :
    let B := directory N sites table w
    let z := bank N a x (tail N w c)
    let counts := fun i : Fin B.reportedCounts.length => B.reportedCounts[i].map z
    (B.weight z : F) * FieldStack.productPaths (FieldPowers.program (scalar N sites table w))
      FieldPowers.factor (fun _ => 1) (1 + ∑ i, (2*(counts i).length+2)) (.visit (Fin.last _)) counts =
      if (∀ j, (ids N sites table a x).count j.val = ((wordBits w).symm (c j)).val) then
        (sites.map (N.read table a x)).prod else 0 := by
  intro B z counts
  rw [FieldPowers.cell_weight,siteObservations]
  have hp : ∀ r ∈ B.records, r.Valid B.boxes z := by simp [B,directory,Record.Valid]
  change (if (∀ r ∈ B.records, r.Valid B.boxes z) ∧ countsValid z B.reportedCounts _ then _ else 0) = _
  by_cases hc : ∀ j, (ids N sites table a x).count j.val = ((wordBits w).symm (c j)).val
  · have hv := (countsValid_iff N sites table w a x c).mpr hc
    rw [ite_eq_left ⟨hp,hv⟩, ite_eq_left hc, (idFacts _).1,(idFacts _).2]
    simp only [Bool.false_eq_true,ite_false,one_mul]
    unfold ids
    rw [List.map_map]
    congr 2
    funext s
    have hh := (Fintype.equivFin F (N.read table a x s)).isLt
    simp only [Function.comp_apply,FieldPowers.entry,scalar,B,directory,List.length_ofFn,hh,dite_true]
    apply (Fintype.equivFin F).injective
    rw [Equiv.apply_symm_apply]
    exact Fin.ext rfl
  · have hv := (countsValid_iff N sites table w a x c).not.mpr hc
    rw [ite_eq_right (fun h => hv h.2), ite_eq_right hc]


end FieldDirectory

end BorderVNP
end Computability
end OAI
