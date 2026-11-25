import OAI.ThreeFlat.Diagonal.TraceDecodeShape
import OAI.ThreeFlat.RAM.InstructionShapes
import OAI.ThreeFlat.Diagonal.TraceProgramText

namespace OAI
/-! # Boolean dispatch from a program supplied as data

Candidates enumerate register indices, jump targets and opcode tags. A literal
operand is a variable word and is excluded from this enumeration. Each
candidate checks exactly the fields that the native row decoder consumes.
-/

namespace ThreeFlat.Diagonal.TraceProgram

open TraceDecodeShape TraceWords RAM
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {w p r k : ℕ} {σ : Type*}

def matchShape (fields : Fin 6 → Fin w → Expr σ) (z : Instr 0 p r k) : Expr σ :=
  allList ((tests z).map fun test => fieldIs (fields test.1) test.2)

theorem matchShape_true (fields : Fin 6 → Fin w → Expr σ) (z : Instr 0 p r k)
    (input : σ → Bool) (data : Memory w) (i : Fin p)
    (h : ∀ j bit, (fields j bit).eval input = bits (data (instructionField (k:=k) i j).val) bit) :
    (matchShape fields z).eval input = true ↔ «matches» (fetchRow data i) z := by
  rw [matchShape, allList_true]
  have test (t : Fin 6 × ℕ) : (fieldIs (fields t.1) t.2).eval input = true ↔
      (fetchRow data i).get t.1 = t.2 := by
    rw [fetchRow_get (k:=k)]
    exact fieldIs_true _ _ _ _ (h t.1)
  constructor
  · intro ha t ht
    exact (test t).mp (ha _ (List.mem_map.mpr ⟨t,ht,rfl⟩))
  · intro hm e he
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp he
    exact (test t).mpr (hm t ht)

/-- Select the candidate verifier by the contents of the six program words. -/
noncomputable def selectSlot (fields : Fin 6 → Fin w → Expr σ) (candidate : Instr 0 p r k → Expr σ) : Expr σ :=
  Expr.disjoin ((InstructionShapes.all p r k).map fun z => (matchShape fields z).and (candidate z))

theorem selectSlot_true (fields : Fin 6 → Fin w → Expr σ) (candidate : Instr 0 p r k → Expr σ)
    (input : σ → Bool) (data : Memory w) (i : Fin p)
    (h : ∀ j bit, (fields j bit).eval input = bits (data (instructionField (k:=k) i j).val) bit) :
    (selectSlot fields candidate).eval input = true ↔
      ∃ ins, decodeRow w p r k (fetchRow data i) = some ins ∧ (candidate (erase ins)).eval input = true := by
  rw [selectSlot, Expr.eval_disjoin_true]
  have hw : (fetchRow data i).b < 2^w := (data (instructionAddress i.val + 2)).isLt
  constructor
  · rintro ⟨e,he,ha⟩
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp he
    obtain ⟨hz,hc⟩ : (matchShape fields z).eval input = true ∧ (candidate z).eval input = true := by
      simpa only [Expr.eval,Bool.and_eq_true] using ha
    refine ⟨_,(matches_iff hw z).mp ((matchShape_true _ _ _ _ _ h).mp hz),?_⟩
    simpa using hc
  · rintro ⟨ins,hi,hc⟩
    let z := erase ins
    refine ⟨(matchShape fields z).and (candidate z),List.mem_map.mpr ⟨z,InstructionShapes.mem_all _,rfl⟩,?_⟩
    have hz := (matchShape_true fields z input data i h).mpr (matches_erase_of_decode hi)
    simp only [Expr.eval,Bool.and_eq_true]
    exact ⟨hz,hc⟩

theorem matchShape_size (fields : Fin 6 → Fin w → Expr σ) (z : Instr 0 p r k)
    (h : ∀ i j, (fields i j).size ≤ 1) : (matchShape fields z).size ≤ 6*(10*w+2)+1 := by
  unfold matchShape
  apply (allList_size_le _ (s:=10*w+1) ?_).trans
  · simp only [List.length_map, Nat.add_assoc]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (tests_length_le z)) 1
  · intro e he
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp he
    exact fieldIs_size _ _ (h t.1)

private theorem selectList_size (L : List (Instr 0 p r k)) {N s : ℕ} (hL : L.length ≤ N)
    (fields : Fin 6 → Fin w → Expr σ) (candidate : Instr 0 p r k → Expr σ)
    (h : ∀ i j, (fields i j).size ≤ 1) (hc : ∀ z, (candidate z).size ≤ s) :
    (Expr.disjoin (L.map fun z => (matchShape fields z).and (candidate z))).size ≤
      N*(6*(10*w+2)+s+3)+1 := by
  have hnode (e : Expr σ) (he : e ∈ L.map fun z => (matchShape fields z).and (candidate z)) :
      e.size ≤ 6*(10*w+2)+s+2 := by
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp he
    have := matchShape_size fields z h
    have := hc z
    simp only [Expr.size]
    omega
  have hb := Expr.size_disjoin_le _ _ hnode
  rw [List.length_map] at hb
  exact hb.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (6*(10*w+2)+s+3) hL) 1)

theorem selectSlot_size (fields : Fin 6 → Fin w → Expr σ) (candidate : Instr 0 p r k → Expr σ)
    (h : ∀ i j, (fields i j).size ≤ 1) {s : ℕ} (hc : ∀ z, (candidate z).size ≤ s) :
    (selectSlot fields candidate).size ≤
      (15*(p+r+k+10)^5)*(6*(10*w+2)+s+3)+1 :=
  selectList_size (InstructionShapes.all p r k) (InstructionShapes.all_length_le p r k) fields candidate h hc

end ThreeFlat.Diagonal.TraceProgram

end OAI
