import OAI.Optimization.LinearProgramming.RAM.Loops
import OAI.Optimization.LinearProgramming.RAM.Array
import Mathlib.Tactic

/-! Sequential writing of a row selector or a copied pivot list in the address bank. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Flush the value in `word` to the pointer in `ptr` and advance the pointer. -/
def emitWord (ptr word : ℕ) : Block := .seq (.op (.addrStore ptr word)) (.op (.incr ptr ptr))

theorem emitWord_spec (P : K → Prop) (s : Memory K) (hs : s.AllData P) (ptr word : ℕ)
    (hlo : ptr ≠ s.index ptr) :
    ∃ t, Block.Eval (Memory.AllData P) (emitWord ptr word) s 2 t ∧
      t.data = s.data ∧ t.index ptr = s.index ptr+1 ∧ t.index (s.index ptr) = s.index word ∧
      ∀ p, p ≠ ptr → p ≠ s.index ptr → t.index p = s.index p := by
  let u := s.putIndex (s.index ptr) (s.index word)
  let t := u.putIndex ptr (u.index ptr+1)
  refine ⟨t, (Block.Eval.op_addrStore s ptr word hs hs).seq (Block.Eval.op_incr u ptr ptr hs hs),
    rfl, ?_, ?_, ?_⟩
  · simp [t, u, hlo]
  · simp [t, u, hlo.symm]
  · intro p h₁ h₂
    simp [t, u, h₁, h₂]

/-- The same loop writes the identity selector, or copies the pivot words to a new block. -/
def selectorCell (copy : Bool) : Block := .seq
  (.op (if copy then .addrLoad 6 5 else .addrCopy 6 1))
  (.seq (emitWord 4 6) (.op (.incr 5 5)))

private theorem selectorCell_spec (P : K → Prop) (s : Memory K) (hs : s.AllData P)
    (copy : Bool) (hdst : 256 ≤ s.index 4) :
    ∃ z, Block.Eval (Memory.AllData P) (selectorCell copy) s 4 z ∧ z.data = s.data ∧
      z.index 4 = s.index 4+1 ∧ z.index 5 = s.index 5+1 ∧
      z.index (s.index 4) = (if copy then s.index (s.index 5) else s.index 1) ∧
      ∀ p, p ≠ 4 → p ≠ 5 → p ≠ 6 → p ≠ s.index 4 → z.index p = s.index p := by
  let v := if copy then s.index (s.index 5) else s.index 1
  let u := s.putIndex 6 v
  have read : Block.Eval (Memory.AllData P) (.op (if copy then .addrLoad 6 5 else .addrCopy 6 1)) s 1 u := by
    cases copy
    · exact Block.Eval.op_addrCopy s 6 1 hs hs
    · exact Block.Eval.op_addrLoad s 6 5 hs hs
  have hu4 : u.index 4 = s.index 4 := by simp [u]
  obtain ⟨t, emit, hd, hp, hw, hframe⟩ := emitWord_spec P u hs 4 6 (by rw [hu4]; omega)
  have ht5 : t.index 5 = s.index 5 := by rw [hframe 5 (by decide) (by rw [hu4]; omega)]; simp [u]
  let z := t.putIndex 5 (t.index 5+1)
  refine ⟨z, read.seq (emit.seq (Block.Eval.op_incr t 5 5 emit.safe_end emit.safe_end)), hd, ?_, ?_, ?_, ?_⟩
  · simpa [z, hu4] using hp
  · simp [z, ht5]
  · rw [hu4] at hw
    simpa [z, u, show s.index 4 ≠ 5 by omega, v] using hw
  · intro p h4 h5 h6 hD
    rw [show z.index p = t.index p from Memory.putIndex_ne _ h5 _, hframe p h4 (hu4 ▸ hD)]
    exact Memory.putIndex_ne _ h6 _

structure StreamEnd (s z : Memory K) (src dst count : ℕ) (copy : Bool) : Prop where
  data : z.data = s.data
  destination : z.index 4 = dst+count
  source : z.index 5 = src+count
  words : ∀ j < count, z.index (dst+j) = if copy then s.index (src+j) else j
  frame : ∀ p, p ≠ 1 → p ≠ 4 → p ≠ 5 → p ≠ 6 → (p < dst ∨ dst+count ≤ p) → z.index p = s.index p

/-- Exact instruction count and full frame for a streaming copy of `count` address-bank words. -/
theorem selectorStream_spec (P : K → Prop) (s : Memory K) (hs : s.AllData P) (copy : Bool)
    (src dst count : ℕ) (hsr : s.index 5 = src) (hde : s.index 4 = dst) (hcount : s.index 7 = count)
    (hlo : 256 ≤ src) (hgap : src+count ≤ dst) :
    ∃ z, Block.Eval (Memory.AllData P) (.forRange 1 7 (selectorCell copy)) s (count*7+2) z ∧
      StreamEnd s z src dst count copy := by
  have safe_of {u : Memory K} (h : u.data = s.data) : u.AllData P := by
    change ∀ i, P (u.data i)
    rw [h]
    exact hs
  let Inv (j : ℕ) (u : Memory K) := u.index 1 = j ∧ StreamEnd s u src dst j copy
  have init : Inv 0 (s.putIndex 1 0) := by
    refine ⟨by simp, rfl, by simpa using hde, by simpa using hsr, by simp, ?_⟩
    intro p h1 _ _ _ _
    exact Memory.putIndex_ne _ h1 _
  obtain ⟨z, eval, _, out⟩ := Block.Eval.forRange_invariant_exact
    (body := selectorCell copy) 1 7 count 4 Inv s hs init
    (fun j u h => ⟨safe_of h.2.data, h.1, (h.2.frame 7 (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by omega))).trans hcount⟩) (fun j hj u h => by
      obtain ⟨uj, hu⟩ := h
      obtain ⟨t, et, td, t4, t5, tw, tf⟩ := selectorCell_spec P u (safe_of hu.data) copy (by rw [hu.destination]; omega)
      have h1 : t.index 1 = j := (tf 1 (by decide) (by decide) (by decide) (by rw [hu.destination]; omega)).trans uj
      let w := t.putIndex 1 (t.index 1+1)
      have ws (p : ℕ) (hp : p ≠ 1) : w.index p = t.index p := Memory.putIndex_ne _ hp _
      refine ⟨t, et, ?_, td.trans hu.data, ?_, ?_, ?_, ?_⟩
      · simp [h1]
      · rw [ws 4 (by decide), t4, hu.destination]; omega
      · rw [ws 5 (by decide), t5, hu.source]; omega
      · intro b hb
        rw [ws _ (by omega)]
        by_cases he : b=j
        · subst b
          rw [← hu.destination, tw, uj, hu.source]
          rw [hu.frame (src+j) (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))]
        · rw [tf _ (by omega) (by omega) (by omega) (by rw [hu.destination]; omega)]
          exact hu.words b (by omega)
      · intro p hp1 hp4 hp5 hp6 hf
        rw [ws _ hp1, tf p hp4 hp5 hp6 (by rw [hu.destination]; omega)]
        exact hu.frame p hp1 hp4 hp5 hp6 (by omega))
  exact ⟨z, eval, out⟩

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
