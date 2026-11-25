import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramTable
import OAI.LinearAlgebra.SpectralBooks.ProgramCode.SignedProgramDecoding

/-! # Canonical padding of decoded transition tables -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram

open SignedMachine

def bounded (n x : ℕ) : Fin (n+1) := ⟨min n x, by omega⟩

private theorem bounded_val {n x : ℕ} (hx : x ≤ n) : (bounded n x).val = x := Nat.min_eq_right hx

private def blankMove (n : ℕ) : Move n := ⟨0, .left, fun _ ↦ (.blank,.left)⟩

private def blankRow (n : ℕ) : Row n := ⟨0,.blank,fun _ ↦ .blank,0,.zero,fun _ ↦ blankMove n⟩

def fromTransition (n : ℕ) (t : Transition) : Move n :=
  ⟨bounded n t.state,t.inputMove, fun i ↦ t.workMoves.getD i.val (.blank,.left)⟩

def fromRule (n : ℕ) (r : Rule) : Row n :=
  let base := blankRow n
  let data := {base with
    state := bounded n r.state
    input := r.inputSymbol
    reads := fun i ↦ r.workSymbols.getD i.val .blank}
  match r.action with
  | .halt o => {data with out := o}
  | .step t => {data with kind := 1, next := fun b ↦ if b then blankMove n else fromTransition n t}
  | .branch t s => {data with kind := 2, next := fun b ↦ if b then fromTransition n s else fromTransition n t}

def fromProgram (n : ℕ) (p : Program) : Table n :=
  ⟨bounded n p.workTapes, bounded n p.table.length,
   fun i ↦ ((p.table[i.val]?).map (fromRule n)).getD (blankRow n)⟩

private theorem activeList_getD {α β : Type*} {n : ℕ} {k : Fin (n+1)} (xs : List α)
    (d : α) (f : α → β) (hk : k.val = xs.length) :
    activeList k (fun i ↦ f (xs.getD i.val d)) = xs.map f := by
  apply List.ext_getElem
  · simp [activeList,hk]
  · intro i hi hj
    have hx : i < xs.length := by simpa using hj
    simp [activeList, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx]

private theorem activeList_getD_id {α : Type*} {n : ℕ} {k : Fin (n+1)} (xs : List α)
    (d : α) (hk : k.val = xs.length) :
    activeList k (fun i ↦ xs.getD i.val d) = xs :=
  (activeList_getD xs d id hk).trans (List.map_id _)

private theorem fromTransition_eq {n : ℕ} {tapes : Fin (n+1)} (t : Transition)
    (hs : t.state ≤ n) (ht : tapes.val = t.workMoves.length) :
    (fromTransition n t).transition tapes = t := by
  cases t with
  | mk st dir ms =>
    simp only [fromTransition, Move.transition, bounded_val hs]
    rw [activeList_getD_id _ _ ht]

private theorem fromRule_eq {n : ℕ} {tapes : Fin (n+1)} (r : Rule)
    (hr : r.state ≤ n) (hw : r.workSymbols.length = tapes.val)
    (ha : ProgramCode.ActionArity tapes.val r.action) (hb : ProgramCode.ActionStateBound n r.action) :
    (fromRule n r).rule tapes = r := by
  cases r with
  | mk s inp reads a =>
    cases a with
    | halt o =>
      simp [fromRule, blankRow, Row.rule, Row.action, bounded_val hr]
      exact activeList_getD_id _ _ hw.symm
    | step t =>
      have ht := fromTransition_eq t hb (Eq.symm ha)
      simp [fromRule, Row.rule, Row.action, bounded_val hr, ht]
      exact activeList_getD_id _ _ hw.symm
    | branch t u =>
      have ht := fromTransition_eq t hb.1 (Eq.symm ha.1)
      have hu := fromTransition_eq u hb.2 (Eq.symm ha.2)
      simp [fromRule, Row.rule, Row.action, bounded_val hr, ht, hu]
      exact activeList_getD_id _ _ hw.symm

end SignedProgram

namespace ProgramCode

open SignedMachine
open private bodyBits ruleBits actionBits transitionBits from
  OAI.LinearAlgebra.SpectralBooks.SignedWitness

/-- Every state named in a program is bounded by the length of its canonical prefix. -/
theorem states_le_code (p : Program) {r : Rule} (hr : r ∈ p.table) :
    r.state ≤ (encode p).length ∧
    ActionStateBound (encode p).length r.action := by
  have hrow : (ruleBits r).length ≤ (p.table.flatMap ruleBits).length := by
    rw [List.length_flatMap]
    exact List.single_le_sum (fun _ _ ↦ Nat.zero_le _) _ (List.mem_map.mpr ⟨r,hr,rfl⟩)
  have h : (ruleBits r).length ≤ (encode p).length := by
    apply hrow.trans
    simp [encode, bodyBits, unary]
    omega
  have hu (v : ℕ) : (unary v).length = v + 1 := by simp [unary]
  simp only [ruleBits, List.length_append, hu] at h
  refine ⟨by omega,?_⟩
  cases he : r.action with
  | halt o => trivial
  | step t =>
    rw [he] at h
    simp only [actionBits, transitionBits, List.length_append, hu] at h
    change t.state ≤ _
    omega
  | branch s t =>
    rw [he] at h
    simp only [actionBits, transitionBits, List.length_append, hu] at h
    exact ⟨by omega, by omega⟩

end ProgramCode

namespace SignedProgram

open SignedMachine

private theorem stateBound_mono {m n : ℕ} {a : Action}
    (h : ProgramCode.ActionStateBound m a) (hmn : m ≤ n) :
    ProgramCode.ActionStateBound n a := by
  cases a with
  | halt => trivial
  | step => exact Nat.le_trans h hmn
  | branch => exact ⟨h.1.trans hmn,h.2.trans hmn⟩

theorem fromProgram_correct {bits : List Bool} {p : Program}
    (h : ProgramCode.decode bits = some p) :
    (fromProgram bits.length p).program = p := by
  obtain ⟨hw, hr⟩ := ProgramCode.decode_size_bounds h
  obtain ⟨hgood, data, hdata⟩ := ProgramCode.decode_eq_some_iff.mp h
  have hlen : (ProgramCode.encode p).length ≤ bits.length := by rw [hdata,List.length_append]; omega
  have hrow (r : Rule) (hr' : r ∈ p.table) :
      (fromRule bits.length r).rule (bounded bits.length p.workTapes) = r := by
    obtain ⟨hs,ht⟩ := ProgramCode.states_le_code p hr'
    obtain ⟨hd,ha⟩ := hgood.2 r hr'
    apply fromRule_eq r (hs.trans hlen)
    · rwa [bounded_val hw]
    · rwa [bounded_val hw]
    · exact stateBound_mono ht hlen
  cases p with
  | mk k rs =>
    simp only [fromProgram, Table.program, bounded_val hw, Program.mk.injEq, true_and]
    apply List.ext_getElem
    · simp [activeList, bounded_val hr]
    · intro i hi hj
      simpa [activeList,List.getElem?_eq_getElem hj] using hrow rs[i] (List.getElem_mem _)

/-- Fix all unused cells by requiring the table to be the standard padding of its program. -/
def Table.Canonical {n : ℕ} (t : Table n) : Prop := t = fromProgram n t.program

/-- There is a unique normalized table for a successful decode. -/
theorem existsUnique_table {bits : List Bool} {p : Program} (h : ProgramCode.decode bits = some p) :
    ∃! t : Table bits.length, t.Canonical ∧ t.program = p := by
  have he := fromProgram_correct h
  refine ⟨fromProgram bits.length p, ⟨by simp [Table.Canonical,he],he⟩,?_⟩
  rintro t ⟨hc,ht⟩
  exact hc.trans (congrArg _ ht)

end SignedProgram

end SpectralBooks
end LinearAlgebra
end OAI
