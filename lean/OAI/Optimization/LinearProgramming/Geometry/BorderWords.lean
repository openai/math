import OAI.Optimization.LinearProgramming.Geometry.BorderStream

/-! Streaming the six address words of a bordered-minor descriptor. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A fixed list of address-register sources, emitted in order. Only the length-six
specialization is used in the assembled program. -/
def emitWords (ptr : ℕ) : List ℕ → Block
  | [] => .skip
  | r :: rs => .seq (emitWord ptr r) (emitWords ptr rs)

structure WordEnd (s t : Memory K) (ptr base : ℕ) (regs : List ℕ) : Prop where
  data : t.data = s.data
  cursor : t.index ptr = base + regs.length
  words : ∀ j : Fin regs.length, t.index (base+j.val) = s.index (regs.get j)
  frame : ∀ p, p ≠ ptr → (p < base ∨ base+regs.length ≤ p) → t.index p = s.index p

theorem emitWords_spec (P : K → Prop) (s : Memory K) (hs : s.AllData P)
    (ptr base : ℕ) (regs : List ℕ) (hptr : s.index ptr = base) (hlo : ptr < base)
    (hi : ∀ r ∈ regs, r ≠ ptr ∧ r < base) :
    ∃ t, Block.Eval (Memory.AllData P) (emitWords ptr regs) s (2*regs.length) t ∧ WordEnd s t ptr base regs := by
  induction regs generalizing base s with
  | nil => exact ⟨s, .skip hs, rfl, by simpa using hptr, fun j => j.elim0, fun _ _ _ => rfl⟩
  | cons r rs ih =>
    obtain ⟨u, he, hu, hcur, hcell, hframe⟩ := emitWord_spec P s hs ptr r (by omega)
    have tailInputs (a) (ha : a ∈ rs) := hi a (List.mem_cons_of_mem r ha)
    obtain ⟨t, het, ht⟩ := ih u he.safe_end (base+1) (hptr ▸ hcur) (by omega)
      (fun a ha => ⟨(tailInputs a ha).1, by have := (tailInputs a ha).2; omega⟩)
    refine ⟨t, ?_, ht.data.trans hu, ?_, ?_, ?_⟩
    · rw [List.length_cons, Nat.mul_succ, Nat.add_comm _ 2]; exact he.seq het
    · rw [ht.cursor, List.length_cons]; omega
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · change t.index (base+0) = s.index r
        rw [Nat.add_zero, ht.frame _ (by omega) (Or.inl (by omega)), ← hptr, hcell]
      · have h := ht.words k
        have hk := tailInputs (rs.get k) (rs.get_mem k)
        have hr : u.index (rs.get k) = s.index (rs.get k) := hframe _ hk.1 (by omega)
        simpa only [List.get_cons_succ', Fin.val_succ, Nat.add_assoc, Nat.add_comm 1 _, hr] using h
    · intro p hne hf
      have hp : p < base+1 ∨ base+1+rs.length ≤ p := by simp only [List.length_cons] at hf; omega
      rw [ht.frame _ hne hp, hframe _ hne (by simp only [List.length_cons] at hf; omega)]

/-- Matrix base, width, minor size, row list, column list, determinant workspace. -/
def emitHeader : Block := emitWords 3 [131, 130, 7, 141, 4, 144]

structure HeaderEnd (s t : Memory K) : Prop where
  data : t.data = s.data
  cursor : t.index 3 = s.index 3 + 6
  words (i : Fin 6) : t.index (s.index 3+i.val) =
    s.index ([131, 130, 7, 141, 4, 144].get i)
  frame : ∀ p, p ≠ 3 → (p < s.index 3 ∨ s.index 3+6 ≤ p) → t.index p = s.index p

theorem emitHeader_spec (P : K → Prop) (s : Memory K) (hs : s.AllData P) (hlo : 256 ≤ s.index 3) :
    ∃ t, Block.Eval (Memory.AllData P) emitHeader s 12 t ∧ HeaderEnd s t := by
  obtain ⟨t, run, endState⟩ := emitWords_spec P s hs 3 (s.index 3) [131,130,7,141,4,144] rfl
    (by omega) (by intro a ha; simp at ha; rcases ha with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  exact ⟨t, run, endState.data, endState.cursor, endState.words, endState.frame⟩

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
